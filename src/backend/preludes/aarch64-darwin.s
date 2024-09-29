awe__syscall_write:
	ldr w0, [sp, -8]
	ldr x1, [sp, -16]
	ldr x2, [sp, -24]
	mov x16, 4
	svc 0x80
	ret
