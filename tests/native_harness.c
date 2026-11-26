/* Runs x86-64 test cases on the host CPU (x86-64 Linux only).

   Reads fixed-size cases from stdin (layout: struct test_case below, written
   by generate_exec.py), and for each one maps the code, data and stack pages
   at fixed addresses, loads all sixteen registers, XMM0..XMM15 and the flags,
   jumps to the entry point, and stops at the first int3 (the code page is
   filled with 0xCC) or fault. Prints one line per case:
     reached <rip> <rax> ... <r15> <flags> <xmm0> ... <xmm15> <data> <stack>
     fault fetch|load|store|divide|alignment <data> <stack>
   in hex, where rip is the int3's address, flags keeps CF PF AF ZF SF OF,
   data is the DATA_SIZE bytes at DATA_BASE and stack the STACK_WINDOW bytes
   at the top of the stack page, where the case stopped. */
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>

#define PAGE 4096UL
#define CODE_BASE 0x100000UL
#define DATA_BASE 0x200000UL
#define STACK_BASE 0x300000UL
#define FLAG_MASK 0x8d5UL
#define DATA_SIZE 256
#define STACK_WINDOW 128

struct test_case {
  uint8_t code[PAGE];
  uint8_t data[PAGE];
  uint8_t stack[PAGE];
  uint64_t regs[16];
  uint64_t rflags;
  uint64_t rip;
  uint32_t data_prot;
  uint32_t stack_prot;
  uint8_t xmm[16][16];
};

/* Register context handed to enter(): regs[0..15], rflags, rip, xmm[0..15]. */
struct context {
  uint64_t regs[16];
  uint64_t rflags;
  uint64_t rip;
  uint8_t xmm[16][16];
};

void enter(struct context *context);
void *jump_target;

__asm__(
    ".text\n"
    ".globl enter\n"
    "enter:\n"
    "  pushq 128(%rdi)\n"
    "  popfq\n"
    "  movq 136(%rdi), %rax\n"
    "  movq %rax, jump_target(%rip)\n"
    "  movdqu 144(%rdi), %xmm0\n"
    "  movdqu 160(%rdi), %xmm1\n"
    "  movdqu 176(%rdi), %xmm2\n"
    "  movdqu 192(%rdi), %xmm3\n"
    "  movdqu 208(%rdi), %xmm4\n"
    "  movdqu 224(%rdi), %xmm5\n"
    "  movdqu 240(%rdi), %xmm6\n"
    "  movdqu 256(%rdi), %xmm7\n"
    "  movdqu 272(%rdi), %xmm8\n"
    "  movdqu 288(%rdi), %xmm9\n"
    "  movdqu 304(%rdi), %xmm10\n"
    "  movdqu 320(%rdi), %xmm11\n"
    "  movdqu 336(%rdi), %xmm12\n"
    "  movdqu 352(%rdi), %xmm13\n"
    "  movdqu 368(%rdi), %xmm14\n"
    "  movdqu 384(%rdi), %xmm15\n"
    "  movq 8(%rdi), %rcx\n"
    "  movq 16(%rdi), %rdx\n"
    "  movq 24(%rdi), %rbx\n"
    "  movq 40(%rdi), %rbp\n"
    "  movq 48(%rdi), %rsi\n"
    "  movq 64(%rdi), %r8\n"
    "  movq 72(%rdi), %r9\n"
    "  movq 80(%rdi), %r10\n"
    "  movq 88(%rdi), %r11\n"
    "  movq 96(%rdi), %r12\n"
    "  movq 104(%rdi), %r13\n"
    "  movq 112(%rdi), %r14\n"
    "  movq 120(%rdi), %r15\n"
    "  movq 32(%rdi), %rsp\n"
    "  movq 0(%rdi), %rax\n"
    "  movq 56(%rdi), %rdi\n"
    "  jmp *jump_target(%rip)\n");

static sigjmp_buf resume;
static int caught_signal;
static siginfo_t caught_info;
static mcontext_t caught_context;
/* XMM0..XMM15 as the signal frame saved them; copied here because the frame
   is gone after siglongjmp. */
static struct _libc_xmmreg caught_xmm[16];

static void on_signal(int signal, siginfo_t *info, void *context) {
  caught_signal = signal;
  caught_info = *info;
  caught_context = ((ucontext_t *)context)->uc_mcontext;
  memcpy(caught_xmm, caught_context.fpregs->_xmm, sizeof caught_xmm);
  siglongjmp(resume, 1);
}

static void fail(const char *what) {
  perror(what);
  exit(2);
}

static void print_bytes(uintptr_t base, size_t size) {
  if (mprotect((void *)(base & ~(PAGE - 1)), PAGE, PROT_READ)) fail("mprotect");
  putchar(' ');
  for (size_t i = 0; i < size; i++) printf("%02x", ((const uint8_t *)base)[i]);
}

static void load_page(uintptr_t base, const uint8_t *bytes, int prot) {
  if (mprotect((void *)base, PAGE, PROT_READ | PROT_WRITE)) fail("mprotect");
  memcpy((void *)base, bytes, PAGE);
  if (mprotect((void *)base, PAGE, prot)) fail("mprotect");
}

int main(void) {
  /* A line per case, so a run that stalls shows the case it stalled on. */
  setvbuf(stdout, NULL, _IOLBF, 0);
  /* Each page is followed by an inaccessible one, as in the model's test
     states, so an access running past a page faults. */
  const uintptr_t bases[] = {CODE_BASE, DATA_BASE, STACK_BASE};
  for (int i = 0; i < 3; i++)
    if (mmap((void *)bases[i], PAGE, PROT_READ | PROT_WRITE,
             MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) != (void *)bases[i] ||
        mmap((void *)(bases[i] + PAGE), PAGE, PROT_NONE,
             MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) != (void *)(bases[i] + PAGE))
      fail("mmap");

  static uint8_t alternate_stack[1 << 16];
  stack_t alternate = {.ss_sp = alternate_stack, .ss_size = sizeof alternate_stack};
  if (sigaltstack(&alternate, NULL)) fail("sigaltstack");
  struct sigaction action = {.sa_sigaction = on_signal, .sa_flags = SA_SIGINFO | SA_ONSTACK};
  sigemptyset(&action.sa_mask);
  const int signals[] = {SIGTRAP, SIGSEGV, SIGBUS, SIGILL, SIGFPE};
  for (int i = 0; i < 5; i++)
    if (sigaction(signals[i], &action, NULL)) fail("sigaction");

  static struct test_case test;
  static struct context context;
  /* Kernel gregs indices of RAX..R15 in ModRM register order. */
  const int order[16] = {REG_RAX, REG_RCX, REG_RDX, REG_RBX, REG_RSP, REG_RBP,
                         REG_RSI, REG_RDI, REG_R8,  REG_R9,  REG_R10, REG_R11,
                         REG_R12, REG_R13, REG_R14, REG_R15};
  while (fread(&test, sizeof test, 1, stdin) == 1) {
    load_page(CODE_BASE, test.code, PROT_READ | PROT_EXEC);
    load_page(DATA_BASE, test.data, (int)test.data_prot);
    load_page(STACK_BASE, test.stack, (int)test.stack_prot);
    memcpy(context.regs, test.regs, sizeof context.regs);
    memcpy(context.xmm, test.xmm, sizeof context.xmm);
    context.rflags = 0x202 | (test.rflags & FLAG_MASK);
    context.rip = test.rip;
    if (sigsetjmp(resume, 1) == 0) enter(&context);
    uint64_t rip = (uint64_t)caught_context.gregs[REG_RIP];
    if (caught_signal == SIGTRAP) {
      printf("reached %llx", (unsigned long long)(rip - 1));
      for (int i = 0; i < 16; i++)
        printf(" %llx", (unsigned long long)caught_context.gregs[order[i]]);
      printf(" %llx", (unsigned long long)(caught_context.gregs[REG_EFL] & FLAG_MASK));
      for (int i = 0; i < 16; i++) {
        const uint32_t *lanes = caught_xmm[i].element;
        printf(" %08x%08x%08x%08x", lanes[3], lanes[2], lanes[1], lanes[0]);
      }
    } else if (caught_signal == SIGSEGV && caught_context.gregs[REG_TRAPNO] == 14) {
      /* Bits 4 and 1 of the page-fault error code mark an instruction fetch
         and a write. */
      uint64_t error = (uint64_t)caught_context.gregs[REG_ERR];
      printf("fault %s", error & 16 ? "fetch" : error & 2 ? "store" : "load");
    } else if (caught_signal == SIGSEGV && caught_context.gregs[REG_TRAPNO] == 13) {
      printf("fault alignment"); /* the #GP of a misaligned legacy SIMD read */
    } else if (caught_signal == SIGFPE && caught_context.gregs[REG_TRAPNO] == 0) {
      printf("fault divide"); /* the divide error (#DE) of DIV and IDIV */
    } else {
      fprintf(stderr, "unexpected signal %d at %llx\n", caught_signal, (unsigned long long)rip);
      return 1;
    }
    print_bytes(DATA_BASE, DATA_SIZE);
    print_bytes(STACK_BASE + PAGE - STACK_WINDOW, STACK_WINDOW);
    putchar('\n');
  }
  return 0;
}
