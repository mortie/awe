// func syscall_write(int, ptr[byte], ulong) long
.global awe$syscall_write
.balign 4
awe$syscall_write:
	ldr w0, [sp, -12] // fd
	ldr x1, [sp, -24] // ptr
	ldr x2, [sp, -32] // size
	mov x8, 64 // WRITE
	svc 0
	bcc awe$syscall_write$ok
	neg x0, x0
awe$syscall_write$ok:
	str x0, [sp, -8]
	ret

// func syscall_open(ptr[byte], int, int) int
.global awe$syscall_open
.balign 4
awe$syscall_open:
	mov x0, -100 // Directory; -100 means CWD
	ldr x1, [sp, -16] // ptr
	ldr w2, [sp, -20] // flags
	ldr w3, [sp, -24] // mode
	mov x8, 56 // OPEN_AT
	svc 0
	bcc awe$syscall_open$ok
	neg w0, w0
awe$syscall_open$ok:
	str w0, [sp, -4]
	ret

// func syscall_close(int) int
.global awe$syscall_close
.balign 4
awe$syscall_close:
	ldr x0, [sp, -8] // fd
	mov x8, 57 // CLOSE
	svc 0
	bcc awe$syscall_close$ok
	neg w0, w0
awe$syscall_close$ok:
	str w0, [sp, -4]
	ret

// Program entry point, called by OS
.global _start
.balign 4
_start:
	bl awe$main
	mov x0, 0
	ldr w0, [sp, -4]
	mov x8, 93 // EXIT
	svc 0
