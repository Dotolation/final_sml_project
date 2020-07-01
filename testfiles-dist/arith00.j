.class public C
.super java/lang/Object

.method public <init>()V
  aload_0
  invokenonvirtual java/lang/Object/<init>()V
  return
.end method

.method public static main([Ljava/lang/String;)V
.limit locals 1000
.limit stack 1000
ldc 1
ldc 2
iadd
invokestatic CSupport/printInt(I)V
ldc 1
ldc 2
isub
invokestatic CSupport/printInt(I)V
ldc 1
ldc 2
imul
invokestatic CSupport/printInt(I)V
ldc 1
ldc 2
idiv
invokestatic CSupport/printInt(I)V
ldc 1
ldc 2
irem
invokestatic CSupport/printInt(I)V
nop
return
.end method
