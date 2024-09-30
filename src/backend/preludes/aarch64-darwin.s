// func syscall_write(int, ptr[void], ulong) long
.global awe$syscall_write
.balign 4
awe$syscall_write:
	ldr w0, [sp, -12]
	ldr x1, [sp, -24]
	ldr x2, [sp, -32]
	mov x16, 4
	svc 0x80
	bcc awe$syscall_write$ok
	neg x0, x0
awe$syscall_write$ok:
	str x0, [sp, -8]
	ret
