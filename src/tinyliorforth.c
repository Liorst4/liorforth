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
    cell_t** body;
};

enum {
    FORTH_FALSE = (cell_t)0,
    FORTH_TRUE = ~FORTH_FALSE,
};

static char* const BOOT_SCRIPT = "";

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

    /* clang-format off */
#define NEXT goto **(++g_vm.ip);
    /* clang-format on */

#define GADGET(name_)      \
    if (g_vm.init_is_done) \
    name_:

#define DEFINE_WORD_FULL(c_name_, forth_name_, flags_)                    \
    static cell_t* c_name_##_body[2] = { &&c_name_, &&ret };              \
    static struct dict_entry c_name_##_dict_entry = (struct dict_entry) { \
        .prev = NULL,                                                     \
        .name = #forth_name_,                                             \
        .flags = (flags_),                                                \
        .body = c_name_##_body,                                           \
    };                                                                    \
    c_name_##_dict_entry.prev = g_vm.dict;                                \
    g_vm.dict = &c_name_##_dict_entry;                                    \
    GADGET(c_name_)

#define DEFINE_WORD(name_, flags_) DEFINE_WORD_FULL(name_, name_, flags_)

    GADGET(ret)
    {
        if (g_vm.return_stack.head) {
            void* return_address = (void*)stack_pop(&g_vm.return_stack);
            goto* return_address;
        }

        goto back_to_repl;
    }

    DEFINE_WORD(/* name_= */ bye, /* flags_= */ 0) { exit(0); }

    DEFINE_WORD(/* name_= */ drop, /* flags_= */ 0)
    {
        (void)stack_pop(&g_vm.data_stack);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ load_literal, /* flags_= */ 0)
    {
        cell_t value = *((cell_t*)++g_vm.ip);
        stack_push(&g_vm.data_stack, value);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ execute, /* flags_= */ 0)
    {
        struct dict_entry* target = (struct dict_entry*)(g_vm.ip + 1);
        cell_t return_address = *(cell_t*)(g_vm.ip + 2);
        stack_push(&g_vm.return_stack, return_address);
        goto*(target->body[0]);
    }

    DEFINE_WORD(/* name_= */ swap, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, b);
        stack_push(&g_vm.data_stack, a);
        NEXT;
    }

    DEFINE_WORD(/* name_= */ rot, /* flags_= */ 0)
    {
        cell_t c = stack_pop(&g_vm.data_stack);
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, b);
        stack_push(&g_vm.data_stack, c);
        stack_push(&g_vm.data_stack, a);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ display,
        /* forth_name_= */ .,
        /* flags_= */ 0)
    {
        cell_t a = stack_pop(&g_vm.data_stack);
        fprintf(stdout, "%lld\n", (long long int)a);
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

    DEFINE_WORD_FULL(/* c_name_= */ peek, /* forth_name_= */ @, /* flags_= */ 0)
    {
        cell_t address = stack_pop(&g_vm.data_stack);
        cell_t value;
        memcpy(&value, (void*)address, sizeof(value));
        stack_push(&g_vm.data_stack, value);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ poke, /* forth_name_= */ !, /* flags_= */ 0)
    {
        cell_t address = stack_pop(&g_vm.data_stack);
        cell_t data = stack_pop(&g_vm.data_stack);
        memcpy((cell_t*)address, &data, sizeof(data));
        NEXT;
    }

    DEFINE_WORD(/* name_= */ base, /* flags_= */ 0)
    {
        stack_push(&g_vm.data_stack, (cell_t)&g_vm.base);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ add, /* forth_name_= */ +, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a + b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ sub, /* forth_name_= */ -, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a - b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ mul, /* forth_name_= */*, /* flags_= */ 0)
    {
        cell_t b = stack_pop(&g_vm.data_stack);
        cell_t a = stack_pop(&g_vm.data_stack);
        stack_push(&g_vm.data_stack, a * b);
        NEXT;
    }

    DEFINE_WORD_FULL(/* c_name_= */ div, /* forth_name_= */ /, /* flags_= */ 0)
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

            char* token = strtok((char*)g_vm.input_buffer.data, " ");
            g_vm.input_buffer.head = (uintptr_t)token - (uintptr_t)g_vm.input_buffer.data;
            while (token) {
                long long number;
                char* number_end;

                /* Handle token */
                number = strtol(token, &number_end, g_vm.base);
                if ((*number_end == '\0') && (errno != ERANGE)) {
                    stack_push(&g_vm.data_stack, (cell_t)number);
                } else {
                    struct dict_entry* word = search_dict(token);
                    assert(word);

                    g_vm.ip = (void**)word->body;
                    goto** g_vm.ip;
                back_to_repl:
                    /* NOP (label at the end of a block was only added in C23) */
                    (void)NULL;
                }

                /* Next token */
                token = strtok(NULL, " ");
                g_vm.input_buffer.head = (uintptr_t)token - (uintptr_t)g_vm.input_buffer.data;
            }
        }
    }

    return 0;
}
