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
ldc 3
invokestatic CSupport/printInt(I)V
ldc2_w 2.3
invokestatic CSupport/printDouble(D)V
ldc 1
invokestatic CSupport/printBool(Z)V
nop
return
.end method
