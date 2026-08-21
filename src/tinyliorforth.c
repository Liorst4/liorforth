/*
 * Copyright (C) 2026 Lior Stern.
 *
 * This file is part of liorforth.
 * liorforth is free software: you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or any later version.
 *
 * liorforth is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * liorforth. If not, see <https://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <errno.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ARRAY_SIZE(x) (sizeof((x)) / sizeof((x)[0]))

typedef intptr_t cell_t;
typedef int8_t byte_t;

struct stack {
    cell_t head;
    cell_t data[0x100];
};

enum {
    DICT_FLAG_IMMEDIATE = 1,
};

struct dict_entry;
struct dict_entry {
    struct dict_entry* prev;
    byte_t name[31];
    cell_t flags;
    cell_t body[0];
};

enum {
    FORTH_FALSE = (cell_t)0,
    FORTH_TRUE = ~FORTH_FALSE,
};

static char* const BOOT_SCRIPT = ": nop ;\n"
                                 ": 1+ 1 + ;\n"
                                 ": 1- 1 - ;\n"
                                 ": swap 1 roll ;\n"
                                 ": rot 2 roll ;\n"
                                 ": nip swap drop ;\n"
                                 ": cr nl emit ;\n"
                                 ": cells sizeof_cell * ;\n"
                                 ": select invert 1 and roll drop ;\n"
                                 ": branch-relative cells r> + >r ;\n"
                                 ": branch-relative? 0 swap cells rot select r> + >r ;\n"
                                 ": postpone ' compile, ; immediate\n"
                                 ": ['] ' postpone literal ; immediate\n";

static struct {
    struct stack data_stack;
    struct stack return_stack;

    struct {
        cell_t head;
        byte_t data[0x100];
    } input_buffer;

    cell_t base;

    struct dict_entry* dict;

    void** ip;

    struct {
        cell_t head;
        byte_t data[0x1000];
    } data_space;

    bool init_is_done;

    cell_t state;
    struct dict_entry* latest;
} g_vm;

static void stack_push(struct stack* s, cell_t value)
{
    assert(s);
    assert((size_t)s->head < ARRAY_SIZE(s->data));
    s->data[s->head++] = value;
}

static cell_t stack_pop(struct stack* s)
{
    assert(s);
    assert(s->head);
    return s->data[--s->head];
}

static struct dict_entry* search_dict(char const* name)
{
    for (struct dict_entry* iter = g_vm.dict; iter; iter = iter->prev) {
        int res = strncmp(name, (char const*)iter->name, sizeof(iter->name));
        if (res == 0) {
            return iter;
        }
    }

    return NULL;
}

static void align_data_space_to(size_t size)
{
    cell_t size_to_add;

    if (0 == (g_vm.data_space.head % size)) {
        return;
    }

    size_to_add = (size - (g_vm.data_space.head % size));
    assert((g_vm.data_space.head + size_to_add) < sizeof(g_vm.data_space.data));
    g_vm.data_space.head += size_to_add;
    assert(0 == (g_vm.data_space.head % size));
}

static void* allot_data(cell_t byte_count, cell_t alignment)
{
    void* result;

    align_data_space_to(alignment);

    result = &g_vm.data_space.data[g_vm.data_space.head];

    assert((g_vm.data_space.head + byte_count) < sizeof(g_vm.data_space.data));
    g_vm.data_space.head += byte_count;

    return result;
}

static cell_t* allot_cell(void)
{
    return allot_data(sizeof(cell_t), alignof(cell_t));
}

static struct dict_entry* allot_dict_header(void)
{
    return allot_data(sizeof(struct dict_entry), alignof(struct dict_entry));
}

static void print_number(FILE* stream, cell_t number)
{
    unsigned long long n;
    assert((2 != g_vm.base) && "Not supported yet"); /* TODO */
    n = number;
    switch (g_vm.base) {
    case 8:
        fprintf(stdout, "%llo", n);
        break;
    case 16:
        fprintf(stdout, "%#llx", n);
        break;
    default:
        fprintf(stdout, "%lld", n);
        break;
    }
}

static char* next_token(bool first_word_in_line)
{
    char* token = strtok(first_word_in_line ? (char*)g_vm.input_buffer.data : NULL, " ");
    g_vm.input_buffer.head = (cell_t)token - (cell_t)g_vm.input_buffer.data;
    return token;
}

int main(void)
{
    FILE* inputs[2];

    /* Init */
    g_vm.data_stack.head = 0;
    g_vm.return_stack.head = 0;
    g_vm.input_buffer.head = 0;
    g_vm.base = 10;
    g_vm.data_space.head = 0;
    g_vm.dict = NULL;
    g_vm.init_is_done = false;
    g_vm.state = FORTH_FALSE;

    /* clang-format off */
#define NEXT goto **(++g_vm.ip);
    /* clang-format on */

#define GADGET(name_)      \
    if (g_vm.init_is_done) \
    name_:

#define DEFINE_WORD_FULL(c_name_, forth_name_, flags_)                 \
    static struct {                                                    \
        struct dict_entry header;                                      \
        cell_t body[2];                                                \
    } c_name_##_dict_entry;                                            \
    _Static_assert(offsetof(typeof(c_name_##_dict_entry), header.body) \
            == offsetof(typeof(c_name_##_dict_entry), body),           \
        "unexpected alignment");                                       \
    c_name_##_dict_entry.header.prev = g_vm.dict;                      \
    strcpy((char*)&c_name_##_dict_entry.header.name, forth_name_);     \
    c_name_##_dict_entry.header.flags = (flags_);                      \
    c_name_##_dict_entry.body[0] = (cell_t)(&&c_name_);                \
    c_name_##_dict_entry.body[1] = (cell_t)(&&ret);                    \
    g_vm.dict = &c_name_##_dict_entry.header;                          \
    GADGET(c_name_)

#define DEFINE_WORD(name_, flags_) DEFINE_WORD_FULL(name_, #name_, flags_)

#define DEFINE_CONSTANT_FULL(c_name_, forth_name_, value_)             \
    static struct {                                                    \
        struct dict_entry header;                                      \
        cell_t body[3];                                                \
    } c_name_##_dict_entry;                                            \
    _Static_assert(offsetof(typeof(c_name_##_dict_entry), header.body) \
            == offsetof(typeof(c_name_##_dict_entry), body),           \
        "unexpected alignment");                                       \
    c_name_##_dict_entry.header.prev = g_vm.dict;                      \
    strcpy((char*)&c_name_##_dict_entry.header.name, forth_name_);     \
    c_name_##_dict_entry.header.flags = 0;                             \
    c_name_##_dict_entry.body[0] = (cell_t)(&&load_literal);           \
    c_name_##_dict_entry.body[1] = (cell_t)(value_);                   \
    c_name_##_dict_entry.body[2] = (cell_t)(&&ret);                    \
    g_vm.dict = &c_name_##_dict_entry.header;

#define DEFINE_CONSTANT(name_, value_) DEFINE_CONSTANT_FULL(name_, #name_, value_)

    GADGET(ret)
    {
        if (g_vm.return_stack.head) {
            void** return_address = (void**)stack_pop(&g_vm.return_stack);
            g_vm.ip = return_address;
            goto** g_vm.ip;
        }

        goto back_to_repl;
    }

    DEFINE_WORD(/* name_= */ bye, /* flags_= */ 0) { exit(0); }

    DEFINE_WORD(/* name_= */ drop, /* flags_= */ 0)
    {
        (void)stack_pop(&g_vm.data_stack);
        NEXT;
    }

    GADGET(/* name_= */ load_literal)
    {
        cell_t value = *((cell_t*)++g_vm.ip);
        stack_push(&g_vm.data_stack, value);
        NEXT;
    }

    GADGET(/* name_= */ call_word)
    {
        struct dict_entry* target = *(struct dict_entry**)(g_vm.ip + 1);
        void** return_address = (g_vm.ip + 2);
        stack_push(&g_vm.return_stack, (cell_t)return_address);
        g_vm.ip = (void**)target->body;
        goto** g_vm.ip;
    }

    DEFINE_WORD(/* name_= */ roll, /* flags_= */ 0)
    {
        cell_t amount;
        cell_t* first;
        cell_t* last;
        cell_t tmp;

        amount = stack_pop(&g_vm.data_stack);

        last = &g_vm.data_stack.data[g_vm.data_stack.head - 1];
        first = &g_vm.data_stack.data[g_vm.data_stack.head - 1 - amount];

        tmp = *first;
        memmove(first, first + 1, amount * sizeof(cell_t));
        *last = tmp;

        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ display,
        /* forth_name_= */ ".",
        /* flags_= */ 0)
    {
        cell_t a = stack_pop(&g_vm.data_stack);
        print_number(stdout, a);
        fflush(stdout);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ emit, /* flags_= */ 0)
    {
        cell_t a = stack_pop(&g_vm.data_stack);
        fprintf(stdout, "%c", (char)a);
        fflush(stdout);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ peek, /* forth_name_= */ "@", /* flags_= */ 0)
    {
        cell_t address = stack_pop(&g_vm.data_stack);
        cell_t value;
        memcpy(&value, (void*)address, sizeof(value));
        stack_push(&g_vm.data_stack, value);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ poke, /* forth_name_= */ "!", /* flags_= */ 0)
    {
        cell_t address = stack_pop(&g_vm.data_stack);
        cell_t data = stack_pop(&g_vm.data_stack);
        memcpy((cell_t*)address, &data, sizeof(data));
        NEXT;
    }

    DEFINE_CONSTANT(/* name_= */ base, /* value_= */ &g_vm.base);

    DEFINE_WORD_FULL(/* c_name_= */ add, /* forth_name_= */ "+", /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a + b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ sub, /* forth_name_= */ "-", /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a - b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ mul, /* forth_name_= */ "*", /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a * b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ div, /* forth_name_= */ "/", /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a / b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ mod, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a % b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */and, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a & b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ or, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a | b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ xor, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a ^ b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ lshift, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a << b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ rshift, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a >> b);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ negate, /* flags_= */ 0)
    {
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, -a);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ invert, /* flags_= */ 0)
    {
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, ~a);
        NEXT;
    }

    DEFINE_CONSTANT_FULL(/* c_name_= */ forth_true, /* forth_name_= */ "true", /* value_= */ FORTH_TRUE);
    DEFINE_CONSTANT_FULL(/* c_name_= */ forth_false, /* forth_name_= */ "false", /* value_= */ FORTH_FALSE);
    DEFINE_CONSTANT_FULL(/* c_name_= */ newline, /* forth_name_= */ "nl", /* value_= */ '\n');
    DEFINE_CONSTANT_FULL(/* c_name_= */ blank, /* forth_name_= */ "bl", /* value_= */ ' ');

    DEFINE_WORD(/* name_= */ here, /* flags_= */ 0)
    {
        stack_push(&g_vm.data_stack, (cell_t)g_vm.data_space.data + g_vm.data_space.head);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ allot, /* flags_= */ 0)
    {
        cell_t size = stack_pop(&g_vm.data_stack);
        (void)allot_data(size, /* alignment= */ 1);
        NEXT;
    }

    DEFINE_CONSTANT(/* name_= */ state, /* value_= */ &g_vm.state);

    DEFINE_WORD_FULL(/* c_name_= */ start_compiling_user_defined_word, /* forth_name_= */ ":", /* flags_= */ 0)
    {
        g_vm.latest = allot_dict_header();
        memset(g_vm.latest, 0, sizeof(*g_vm.latest));
        char* name = next_token(/* first_word_in_line= */ false);
        assert(strlen(name) < sizeof(g_vm.latest->name));
        strncpy((char*)g_vm.latest->name, name, sizeof(g_vm.latest->name));
        g_vm.state = FORTH_TRUE;
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ end_compiling_user_defined_word, /* forth_name_= */ ";", /* flags_= */ DICT_FLAG_IMMEDIATE)
    {
        /* clang-format off */
        *allot_cell() = (cell_t)&&ret;
        /* clang-format on */

        g_vm.latest->prev = g_vm.dict;
        g_vm.dict = g_vm.latest;
        g_vm.state = FORTH_FALSE;
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ push_to_return_stack,
        /* forth_name_= */ ">r",
        /* flags_= */ 0)
    {
        cell_t value = stack_pop(&g_vm.data_stack);
        cell_t calling_word_address = stack_pop(&g_vm.return_stack);
        stack_push(&g_vm.return_stack, value);
        stack_push(&g_vm.return_stack, calling_word_address);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ pop_from_return_stack,
        /* forth_name_= */ "r>",
        /* flags_= */ 0)
    {
        cell_t calling_word_address = stack_pop(&g_vm.return_stack);
        cell_t value = stack_pop(&g_vm.return_stack);
        stack_push(&g_vm.data_stack, value);
        stack_push(&g_vm.return_stack, calling_word_address);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ show_stack, /* forth_name_= */ ".s", /* flags_= */ 0)
    {
        fputc('<', stdout);
        print_number(stdout, g_vm.data_stack.head);
        fputs("> ", stdout);
        for (unsigned int i = 0; i < g_vm.data_stack.head; ++i) {
            print_number(stdout, g_vm.data_stack.data[i]);
            fputc(' ', stdout);
        }

        fflush(stdout);
        NEXT;
    }

    DEFINE_CONSTANT(/* name_= */ sizeof_cell, /* value_= */ sizeof(cell_t));

    DEFINE_WORD(/* name_= */ literal, /* flags_= */ DICT_FLAG_IMMEDIATE)
    {
        cell_t number = stack_pop(&g_vm.data_stack);
        /* clang-format off */
        *allot_cell() = (cell_t)&&load_literal;
        /* clang-format on */
        *allot_cell() = number;
        NEXT;
    }

    DEFINE_WORD(/* name_ */ immediate, /* flags_= */ 0)
    {
        g_vm.latest->flags |= DICT_FLAG_IMMEDIATE;
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ forth_search_dict, /* forth_name_= */ "'", /* flags_= */ 0)
    {
        char* name = next_token(/* first_word_in_line= */ false);
        struct dict_entry* search_result = search_dict(name);
        assert(search_result);
        stack_push(&g_vm.data_stack, (cell_t)search_result);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ append_dict_call, /* forth_name= */ "compile,", /* flags= */ 0)
    {
        struct dict_entry* xt = (struct dict_entry*)stack_pop(&g_vm.data_stack);
        /* clang-format off */
        *allot_cell() = (cell_t)&&call_word;
        /* clang-format on */
        *allot_cell() = (cell_t)xt;
        NEXT;
    }

    DEFINE_WORD(/* name_= */ dup, /* flags_= */ 0)
    {
        cell_t x = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, x);
        stack_push(&g_vm.data_stack, x);
        NEXT;
    }

#undef DEFINE_CONSTANT
#undef DEFINE_WORD
#undef DEFINE_WORD_FULL
#undef GADGET
#undef NEXT

    g_vm.init_is_done = true;

    inputs[0] = fmemopen(BOOT_SCRIPT, strlen(BOOT_SCRIPT), "rb");
    assert(inputs[0]);
    inputs[1] = stdin;

    for (unsigned int i = 0; i < ARRAY_SIZE(inputs); ++i) {
        while (true) {
            g_vm.input_buffer.head = 0;
            memset(g_vm.input_buffer.data, 0, sizeof(g_vm.input_buffer.data));
            if (!fgets((char*)g_vm.input_buffer.data, sizeof(g_vm.input_buffer.data),
                    inputs[i])) {
                break;
            }

            /* Check that the input wasn't truncated */
            assert(g_vm.input_buffer.data[sizeof(g_vm.input_buffer.data) - 1] == 0);
            assert(g_vm.input_buffer
                       .data[strlen((char const*)g_vm.input_buffer.data) - 1]
                == '\n');

            /* Remove trailing newline */
            g_vm.input_buffer.data[strlen((char const*)g_vm.input_buffer.data) - 1] = 0;

            char* token = next_token(/* first_word_in_line= */ true);
            while (token) {
                long long number;
                char* number_end;

                /* Handle token */
                assert((2 != g_vm.base) && "Not supported yet"); /* TODO */
                number = strtol(token, &number_end, g_vm.base);
                if ((*number_end == '\0') && (errno != ERANGE)) {
                    if (g_vm.state == FORTH_TRUE) {
                        /* clang-format off */
                        *allot_cell() = (cell_t)&&load_literal;
                        /* clang-format on */
                        *allot_cell() = number;
                    } else {
                        stack_push(&g_vm.data_stack, (cell_t)number);
                    }
                } else {
                    struct dict_entry* word = search_dict(token);
                    assert(word);
                    if ((g_vm.state == FORTH_TRUE) && !(word->flags & DICT_FLAG_IMMEDIATE)) {
                        /* clang-format off */
                        *allot_cell() = (cell_t)&&call_word;
                        /* clang-format on */
                        *allot_cell() = (cell_t)word;
                    } else {
                        g_vm.ip = (void**)word->body;
                        goto** g_vm.ip;
                    }

                back_to_repl:
                    /* NOP (label at the end of a block was only added in C23) */
                    (void)NULL;
                }

                /* Next token */
                token = next_token(/* first_word_in_line= */ false);
            }
        }
    }

    return 0;
}
