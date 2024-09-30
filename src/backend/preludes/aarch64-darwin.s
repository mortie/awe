// func syscall_write(int, ptr[void], ulong) int
.global awe__syscall_write
.balign 4
awe__syscall_write:
	ldr w0, [sp, -8]
	ldr x1, [sp, -16]
	ldr x2, [sp, -24]
	mov x16, 4
	svc 0x80
	// TODO: write return valuet o [sp, -4]
	ret
