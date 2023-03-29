bits 16

mov [4], cs
mov [4], ss
mov [4], ds
mov [4], es

mov cs, [4]
mov ss, [4]
mov ds, [4]
mov es, [4]

mov cs, [bx + si]

mov cs, [bx + si + 4999]

mov [bx + si + 4999], ds

mov [bx + si + 3], ds
mov [bx + si], cs
mov es, [bx + si]
mov cs, ax
mov bx, ds
