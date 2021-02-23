(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (node 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (next Addr) (data Int))
  )
))
(declare-fun inv_main103 (Heap Int Int Addr Int Int Addr Int Addr) Bool)
(declare-fun inv_main107 (Heap Int Int Addr Int Int Addr Int Addr Addr) Bool)
(declare-fun inv_main110 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main12 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main15 (Heap Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Int Int Int Int Addr) Bool)
(declare-fun inv_main21 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap Int Int Int Int Addr Addr) Bool)
(declare-fun inv_main28 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main31 (Heap Int Int Int Int Addr Addr Int Addr Int) Bool)
(declare-fun inv_main34 (Heap Int Int Int Int Addr Addr Int Addr) Bool)
(declare-fun inv_main36 (Heap Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main4 (Heap Int Int) Bool)
(declare-fun inv_main51 (Heap Int Int Addr Int Int Int Int Int Int Addr) Bool)
(declare-fun inv_main54 (Heap Int Int Addr Int Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main57 (Heap Int Int Addr Int Int Int Int Int Int Addr) Bool)
(declare-fun inv_main61 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main64 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main67 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main69 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main71 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main72 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main73 (Heap Int Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main75 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main76 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main78 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main83 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main88 (Heap Int Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main91 (Heap Int Int Addr Int Int Addr Int) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0 2 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Heap) (var5 Int) (var6 node) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr)) (or (not (and (inv_main4 var4 var1 var0) (and (not (= nullAddr var10)) (and (and (and (and (and (and (= var9 (newHeap (alloc var4 (O_node var6)))) (= var8 var1)) (= var2 var0)) (= var5 var1)) (= var3 var0)) (= var7 var0)) (= var10 (newAddr (alloc var4 (O_node var6)))))))) (inv_main12 var9 var8 var2 var5 var3 var7 var10))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Int) (var14 Int) (var15 Addr) (var16 Int) (var17 Addr)) (or (not (and (inv_main34 var12 var10 var0 var16 var13 var17 var6 var4 var15) (and (and (and (and (and (and (and (and (= var8 (write var12 var15 (O_node (node (next (getnode (read var12 var15))) var4)))) (= var9 var10)) (= var11 var0)) (= var14 var16)) (= var3 var13)) (= var7 var17)) (= var5 var6)) (= var1 var4)) (= var2 var15)))) (inv_main36 var8 var9 var11 var14 var3 var7 var5 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int)) (or (not (and (inv_main78 var11 var7 var1 var8 var16 var5 var10 var2) (and (and (not (= var3 var15)) (not (= (+ var9 1) var0))) (and (and (and (and (and (and (and (and (= var14 var11) (= var13 var7)) (= var6 var1)) (= var15 var8)) (= var4 var16)) (= var0 var5)) (= var12 var10)) (= var9 var2)) (= var3 (next (getnode (read var11 var10)))))))) (inv_main75 var14 var13 var6 var15 var4 var0 var3 (+ var9 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Heap) (var15 Heap) (var16 Int) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int)) (or (not (and (inv_main69 var14 var12 var0 var13 var20 var4 var16 var19 var10 var18 var17 var6) (and (and (and (and (and (and (and (and (= var15 (write var14 var18 (O_node (node var6 (data (getnode (read var14 var18))))))) (= var11 var12)) (= var9 var0)) (= var3 var13)) (= var7 var20)) (= var2 var4)) (= var5 var16)) (= var1 var19)) (= var8 var10)))) (inv_main75 var15 var11 var9 var3 var7 var2 var3 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Addr) (var20 Addr) (var21 Int) (var22 Int) (var23 Int)) (or (not (and (inv_main73 var14 var9 var1 var11 var23 var3 var18 var22 var6 var20 var19 var4) (and (and (and (and (and (and (and (and (and (and (and (= var2 (write var14 var11 (O_node (node var20 (data (getnode (read var14 var11))))))) (= var10 var9)) (= var8 var1)) (= var17 var11)) (= var0 var23)) (= var21 var3)) (= var5 var18)) (= var15 var22)) (= var13 var6)) (= var7 var20)) (= var16 var19)) (= var12 var4)))) (inv_main75 var2 var10 var8 var7 var0 var21 var7 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Int)) (or (not (and (inv_main72 var15 var12 var1 var13 var23 var3 var18 var22 var8 var21 var20 var6) (and (and (and (and (and (and (and (and (and (and (and (= var9 (write var15 var21 (O_node (node var21 (data (getnode (read var15 var21))))))) (= var7 var12)) (= var10 var1)) (= var16 var13)) (= var14 var23)) (= var11 var3)) (= var17 var18)) (= var0 var22)) (= var2 var8)) (= var19 var21)) (= var5 var20)) (= var4 var6)))) (inv_main75 var9 var7 var10 var19 var14 var11 var19 0))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Heap) (var11 Int) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Int)) (or (not (and (inv_main83 var10 var6 var0 var7 var16 var4 var9 var1) (and (and (and (and (and (and (and (and (= var2 var10) (= var3 var6)) (= var11 var0)) (= var13 var7)) (= var8 var16)) (= var5 var4)) (= var12 var9)) (= var14 var1)) (= var15 (next (getnode (read var10 var9))))))) (inv_main88 var2 var3 var11 var13 var8 var5 var15 (+ var14 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main91 var11 var8 var0 var9 var16 var4 var10 var1) (and (not (= var14 var7)) (and (and (and (and (and (and (and (and (= var13 var11) (= var12 var8)) (= var5 var0)) (= var7 var9)) (= var2 var16)) (= var15 var4)) (= var3 var10)) (= var6 var1)) (= var14 (next (getnode (read var11 var10)))))))) (inv_main88 var13 var12 var5 var7 var2 var15 var14 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Int)) (or (not (inv_main54 var5 var2 var1 var3 var11 var4 var8 var10 var9 var0 var6 var7)) (inv_main54 var5 var2 var1 var3 var11 var4 var8 var10 var9 var0 var6 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int) (var14 Int) (var15 node) (var16 Addr) (var17 Int) (var18 Heap) (var19 Int) (var20 Int) (var21 Addr) (var22 Int) (var23 Heap) (var24 Int) (var25 Int) (var26 Heap) (var27 Int) (var28 Int) (var29 Addr) (var30 Int) (var31 Addr) (var32 Int)) (or (not (and (inv_main22 var26 var22 var0 var8 var27 var29 var4) (and (and (and (= nullAddr var31) (and (and (and (and (and (and (and (and (and (and (= var11 (newHeap (alloc var18 (O_node var15)))) (= var17 var10)) (= var24 var30)) (= var16 var2)) (= var13 var9)) (= var20 var1)) (= var3 3)) (= var19 var9)) (= var12 var1)) (= var5 var9)) (= var31 (newAddr (alloc var18 (O_node var15)))))) (and (and (and (and (and (= var18 var23) (= var10 var14)) (= var30 var28)) (= var2 var21)) (= var9 5)) (and (and (and (and (<= 0 (+ (+ 2 (* (- 1) (+ var14 (* (- 2) var32)))) (- 1))) (<= 0 (+ (+ 2 (* 1 (+ var14 (* (- 2) var32)))) (- 1)))) (or (not (<= 0 (+ (+ var14 (* (- 2) var32)) (- 1)))) (<= 0 (+ var14 (- 1))))) (or (not (<= 0 (+ (* (- 1) (+ var14 (* (- 2) var32))) (- 1)))) (<= 0 (+ (* (- 1) var14) (- 1))))) (= var1 var32)))) (and (and (and (and (and (and (= var23 (write var26 var4 (O_node (node var29 (data (getnode (read var26 var4))))))) (= var14 var22)) (= var28 var0)) (= var25 var8)) (= var6 var27)) (= var21 var29)) (= var7 var4))))) (inv_main54 var11 var17 var24 var16 var13 var20 var3 var19 var12 var5 var31 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (inv_main21 var2 var1 var0 var5 var3 var6 var4) (not (<= 0 (+ (+ var5 (- 1)) (- 1)))))) (inv_main22 var2 var1 var0 var5 var3 var6 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (and (inv_main61 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (and (= var2 nullAddr) (and (= var7 nullAddr) (not (<= 0 (+ var8 (- 1)))))))) (inv_main72 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (or (not (inv_main12 var2 var1 var0 var5 var3 var6 var4)) (inv_main18 (write var2 var4 (O_node (node nullAddr (data (getnode (read var2 var4)))))) var1 var0 var5 var3 var6 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int)) (or (not (and (inv_main78 var11 var7 var1 var8 var16 var5 var10 var2) (and (or (= var3 var15) (= (+ var9 1) var0)) (and (and (and (and (and (and (and (and (= var14 var11) (= var13 var7)) (= var6 var1)) (= var15 var8)) (= var4 var16)) (= var0 var5)) (= var12 var10)) (= var9 var2)) (= var3 (next (getnode (read var11 var10)))))))) (inv_main76 var14 var13 var6 var15 var4 var0 var3 (+ var9 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (inv_main31 var3 var2 var0 var8 var4 var9 var6 var5 var7 var1)) (inv_main31 var3 var2 var0 var8 var4 var9 var6 var5 var7 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 node) (var8 Addr) (var9 Int) (var10 Int) (var11 Heap) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr)) (or (not (and (inv_main21 var11 var10 var0 var14 var12 var15 var8) (and (and (= nullAddr var16) (and (and (and (and (and (and (and (and (= var6 (newHeap (alloc var11 (O_node var7)))) (= var13 var10)) (= var9 var0)) (= var1 var14)) (= var2 var12)) (= var4 var15)) (= var3 var8)) (= var5 var12)) (= var16 (newAddr (alloc var11 (O_node var7)))))) (<= 0 (+ (+ var14 (- 1)) (- 1)))))) (inv_main31 var6 var13 var9 var1 var2 var4 var3 var5 var16 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (inv_main67 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5)) (inv_main69 (write var4 var7 (O_node (node var9 (data (getnode (read var4 var7)))))) var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (and (inv_main61 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (and (not (= var2 nullAddr)) (and (= var7 nullAddr) (not (<= 0 (+ var8 (- 1)))))))) (inv_main71 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main75 var6 var2 var0 var3 var7 var4 var5 var1) (not (= var0 (data (getnode (read var6 var5))))))) (inv_main110 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main76 var6 var2 var0 var3 var7 var4 var5 var1) (not (= var7 (data (getnode (read var6 var5))))))) (inv_main110 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main88 var6 var2 var0 var3 var7 var4 var5 var1) (not (= var0 (data (getnode (read var6 var5))))))) (inv_main110 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main91 var11 var8 var0 var9 var16 var4 var10 var1) (and (not (= (+ var6 1) (+ 1 var12))) (and (= var14 var7) (and (and (and (and (and (and (and (and (= var13 var11) (= var12 var8)) (= var5 var0)) (= var7 var9)) (= var2 var16)) (= var15 var4)) (= var3 var10)) (= var6 var1)) (= var14 (next (getnode (read var11 var10))))))))) (inv_main110 var13 var12 var5 var7 var2 var15 var14 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Int) (var14 Addr) (var15 Heap) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Int) (var24 Int)) (or (not (and (inv_main64 var15 var13 var1 var14 var24 var5 var17 var23 var10 var22 var20 var6) (and (and (and (and (and (and (and (and (and (and (and (and (= var4 var15) (= var19 var13)) (= var12 var1)) (= var11 var14)) (= var3 var24)) (= var18 var5)) (= var16 var17)) (= var0 var23)) (= var21 var10)) (= var9 var22)) (= var7 var20)) (= var8 var6)) (= var2 (next (getnode (read var15 var6))))))) (inv_main61 var4 var19 var12 var11 var3 var18 var16 var0 (+ var21 (- 1)) var9 var7 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Int) (var26 Heap) (var27 Int) (var28 Heap) (var29 Heap) (var30 Addr) (var31 Int) (var32 Int)) (or (not (and (inv_main57 var26 var24 var1 var9 var32 var4 var16 var31 var8 var0 var11) (and (and (and (and (and (and (and (and (and (and (and (= var28 var29) (= var5 var27)) (= var6 var21)) (= var2 var13)) (= var25 var14)) (= var20 var23)) (= var18 var15)) (= var3 var17)) (= var19 var10)) (= var12 var30)) (= var7 nullAddr)) (and (and (and (and (and (and (and (and (and (and (= var29 (write var26 var11 (O_node (node (next (getnode (read var26 var11))) var0)))) (= var27 var24)) (= var21 var1)) (= var13 var9)) (= var14 var32)) (= var23 var4)) (= var15 var16)) (= var17 var31)) (= var10 var8)) (= var22 var0)) (= var30 var11))))) (inv_main61 var28 var5 var6 var2 var25 var20 var18 var3 var19 var12 var7 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Heap) (var14 Heap) (var15 Int) (var16 Int) (var17 Int) (var18 node) (var19 Int) (var20 Int) (var21 Int) (var22 Int) (var23 Addr) (var24 Int) (var25 Heap) (var26 Int) (var27 Int) (var28 Heap) (var29 Int) (var30 Int) (var31 Addr) (var32 Int)) (or (not (and (inv_main22 var28 var24 var0 var11 var29 var31 var2) (and (and (and (not (= nullAddr var5)) (and (and (and (and (and (and (and (and (and (and (= var14 (newHeap (alloc var13 (O_node var18)))) (= var3 var20)) (= var16 var15)) (= var10 var9)) (= var1 var7)) (= var22 var4)) (= var19 3)) (= var27 var7)) (= var6 var4)) (= var21 var7)) (= var5 (newAddr (alloc var13 (O_node var18)))))) (and (and (and (and (and (= var13 var25) (= var20 var17)) (= var15 var30)) (= var9 var23)) (= var7 5)) (and (and (and (and (<= 0 (+ (+ 2 (* (- 1) (+ var17 (* (- 2) var32)))) (- 1))) (<= 0 (+ (+ 2 (* 1 (+ var17 (* (- 2) var32)))) (- 1)))) (or (not (<= 0 (+ (+ var17 (* (- 2) var32)) (- 1)))) (<= 0 (+ var17 (- 1))))) (or (not (<= 0 (+ (* (- 1) (+ var17 (* (- 2) var32))) (- 1)))) (<= 0 (+ (* (- 1) var17) (- 1))))) (= var4 var32)))) (and (and (and (and (and (and (= var25 (write var28 var2 (O_node (node var31 (data (getnode (read var28 var2))))))) (= var17 var24)) (= var30 var0)) (= var26 var11)) (= var8 var29)) (= var23 var31)) (= var12 var2))))) (inv_main51 var14 var3 var16 var10 var1 var22 var19 var27 var6 var21 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main75 var6 var2 var0 var3 var7 var4 var5 var1) (= var0 (data (getnode (read var6 var5)))))) (inv_main78 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (and (inv_main61 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (<= 0 (+ var8 (- 1))))) (inv_main64 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var5 var5))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Int) (var12 Int) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (inv_main36 var9 var8 var0 var13 var10 var14 var7 var6) (and (and (and (and (and (and (and (= var1 (write var9 var6 (O_node (node var14 (data (getnode (read var9 var6))))))) (= var3 var8)) (= var12 var0)) (= var11 var13)) (= var5 var10)) (= var15 var14)) (= var2 var7)) (= var4 var6)))) (inv_main21 var1 var3 var12 (+ var11 (- 1)) var5 var4 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Int)) (or (not (and (inv_main18 var9 var7 var0 var12 var10 var5 var3) (and (and (and (and (and (and (= var6 (write var9 var3 (O_node (node (next (getnode (read var9 var3))) var5)))) (= var1 var7)) (= var8 var0)) (= var4 var12)) (= var2 var10)) (= var13 var5)) (= var11 var3)))) (inv_main21 var6 var1 var8 var4 var2 var11 var11))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Heap) (var14 Addr) (var15 Int) (var16 Int)) (or (not (and (inv_main91 var11 var8 var0 var9 var16 var4 var10 var1) (and (not (= nullAddr var7)) (and (= (+ var6 1) (+ 1 var12)) (and (= var14 var7) (and (and (and (and (and (and (and (and (= var13 var11) (= var12 var8)) (= var5 var0)) (= var7 var9)) (= var2 var16)) (= var15 var4)) (= var3 var10)) (= var6 var1)) (= var14 (next (getnode (read var11 var10)))))))))) (inv_main103 var13 var12 var5 var7 var2 var15 var14 (+ var6 1) var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main88 var6 var2 var0 var3 var7 var4 var5 var1) (= var0 (data (getnode (read var6 var5)))))) (inv_main91 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (inv_main71 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5)) (inv_main73 (write var4 var9 (O_node (node var2 (data (getnode (read var4 var9)))))) var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (or (not (inv_main51 var5 var2 var1 var3 var10 var4 var7 var9 var8 var0 var6)) (inv_main57 (write var5 var6 (O_node (node nullAddr (data (getnode (read var5 var6)))))) var2 var1 var3 var10 var4 var7 var9 var8 var0 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 node) (var7 Addr) (var8 Int) (var9 Heap) (var10 Int) (var11 Heap) (var12 Int) (var13 Int) (var14 Int) (var15 Addr) (var16 Int)) (or (not (and (inv_main21 var11 var10 var0 var14 var12 var15 var7) (and (and (not (= nullAddr var4)) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var11 (O_node var6)))) (= var16 var10)) (= var13 var0)) (= var2 var14)) (= var8 var12)) (= var5 var15)) (= var3 var7)) (= var1 var12)) (= var4 (newAddr (alloc var11 (O_node var6)))))) (<= 0 (+ (+ var14 (- 1)) (- 1)))))) (inv_main28 var9 var16 var13 var2 var8 var5 var3 var1 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (inv_main28 var2 var1 var0 var7 var3 var8 var5 var4 var6)) (inv_main34 (write var2 var6 (O_node (node nullAddr (data (getnode (read var2 var6)))))) var1 var0 var7 var3 var8 var5 var4 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Int) (var16 Int) (var17 Int) (var18 Int)) (or (not (and (inv_main103 var14 var8 var0 var11 var18 var3 var13 var2 var10) (and (not (= var1 var12)) (and (and (and (and (and (and (and (and (and (= var6 var14) (= var4 var8)) (= var17 var0)) (= var7 var11)) (= var5 var18)) (= var16 var3)) (= var9 var13)) (= var15 var2)) (= var12 var10)) (= var1 (next (getnode (read var14 var10)))))))) (inv_main107 var6 var4 var17 var7 var5 var16 var9 var15 var12 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Int) (var26 Int) (var27 Heap) (var28 Heap) (var29 Heap) (var30 Int) (var31 Int)) (or (not (and (inv_main107 var28 var25 var1 var11 var31 var4 var13 var2 var10 var5) (and (not (= var16 var3)) (and (and (and (and (and (and (and (and (and (and (and (= var29 var28) (= var14 var25)) (= var30 var1)) (= var12 var11)) (= var6 var31)) (= var8 var4)) (= var7 var13)) (= var24 var2)) (= var0 var10)) (= var21 var5)) (= var20 (next (getnode (read var28 var5))))) (and (and (and (and (and (and (and (and (and (and (= var27 (write var29 var21 defObj)) (= var15 var14)) (= var17 var30)) (= var22 var12)) (= var26 var6)) (= var9 var8)) (= var19 var7)) (= var18 var24)) (= var3 var0)) (= var23 var21)) (= var16 var20)))))) (inv_main107 var27 var15 var17 var22 var26 var9 var19 var18 var3 var16))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Int)) (or (not (inv_main15 var2 var1 var0 var5 var3 var7 var4 var6)) (inv_main15 var2 var1 var0 var5 var3 var7 var4 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 node) (var10 Int)) (or (not (and (inv_main4 var5 var2 var1) (and (= nullAddr var8) (and (and (and (and (and (and (= var6 (newHeap (alloc var5 (O_node var9)))) (= var4 var2)) (= var7 var1)) (= var0 var2)) (= var10 var1)) (= var3 var1)) (= var8 (newAddr (alloc var5 (O_node var9)))))))) (inv_main15 var6 var4 var7 var0 var10 var3 var8 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (or (not (and (inv_main61 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (and (not (= var7 nullAddr)) (not (<= 0 (+ var8 (- 1))))))) (inv_main67 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (or (not (and (inv_main76 var6 var2 var0 var3 var7 var4 var5 var1) (= var7 (data (getnode (read var6 var5)))))) (inv_main83 var6 var2 var0 var3 var7 var4 var5 var1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main12 var2 var1 var0 var5 var3 var6 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main18 var2 var1 var0 var5 var3 var6 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (inv_main28 var2 var1 var0 var7 var3 var8 var5 var4 var6) (not (is-O_node (read var2 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (inv_main34 var2 var1 var0 var7 var3 var8 var5 var4 var6) (not (is-O_node (read var2 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main36 var2 var1 var0 var6 var3 var7 var5 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr)) (not (and (inv_main22 var2 var1 var0 var5 var3 var6 var4) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (not (and (inv_main51 var5 var2 var1 var3 var10 var4 var7 var9 var8 var0 var6) (not (is-O_node (read var5 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (not (and (inv_main57 var5 var2 var1 var3 var10 var4 var7 var9 var8 var0 var6) (not (is-O_node (read var5 var6)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main64 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main67 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var7)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main69 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var9)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main71 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var9)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main73 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var2)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Int)) (not (and (inv_main72 var4 var1 var0 var2 var11 var3 var6 var10 var8 var9 var7 var5) (not (is-O_node (read var4 var9)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main75 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main78 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main76 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main83 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main88 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (and (inv_main91 var6 var2 var0 var3 var7 var4 var5 var1) (not (is-O_node (read var6 var5)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int)) (not (and (inv_main103 var7 var2 var0 var4 var8 var5 var6 var1 var3) (not (is-O_node (read var7 var3)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int)) (not (and (inv_main107 var7 var2 var0 var4 var9 var5 var6 var1 var3 var8) (not (is-O_node (read var7 var8)))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int)) (not (inv_main110 var6 var2 var0 var3 var7 var4 var5 var1))))
(check-sat)
