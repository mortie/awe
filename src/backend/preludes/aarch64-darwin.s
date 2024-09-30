// func syscall_write(int, ptr[void], ulong) long
.global awe__syscall_write
.balign 4
awe__syscall_write:
	ldr w0, [sp, -12]
	ldr x1, [sp, -24]
	ldr x2, [sp, -32]
	mov x16, 4
	svc 0x80
	bcc awe__syscall_write__ok
	neg x0, x0
awe__syscall_write__ok:
	str x0, [sp, -8]
	ret
