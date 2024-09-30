// func syscall_write(int, ptr[void], ulong) long
.global awe$syscall_write
.balign 4
awe$syscall_write:
	ldr w0, [sp, -12]
	ldr x1, [sp, -24]
	ldr x2, [sp, -32]
	mov x16, 4 // WRITE
	svc 0x80
	bcc awe$syscall_write$ok
	neg x0, x0
awe$syscall_write$ok:
	str x0, [sp, -8]
	ret

// func syscall_open(ptr[void], int, int) int
.global awe$syscall_open
.balign 4
awe$syscall_open:
	ldr x0, [sp, -16]
	ldr w1, [sp, -20]
	ldr w2, [sp, -24]
	mov x16, 5 // OPEN
	svc 0x80
	bcc awe$syscall_open$ok
	neg w0, w0
awe$syscall_open$ok:
	str w0, [sp, -4]
	ret

// func syscall_close(int) int
.global awe$syscall_close
.balign 4
awe$syscall_close:
	ldr x0, [sp, -8]
	mov x16, 6 // CLOSE
	svc 0x80
	bcc awe$syscall_close$ok
	neg w0, w0
awe$syscall_close$ok:
	str w0, [sp, -4]
	ret
