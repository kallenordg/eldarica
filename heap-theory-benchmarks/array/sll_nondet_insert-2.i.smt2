(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (next Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defHeapObject)))
(define-fun read ((h Heap) (p Addr)) HeapObject
  (ite (valid h p)
       (select (HeapContents h) p)
       defHeapObject))
(define-fun write ((h Heap) (p Addr) (o HeapObject)) Heap
  (ite (valid h p)
       (HeapCtor (HeapSize h) (store (HeapContents h) p o))
       h))
(define-fun alloc   ((h Heap) (o HeapObject)) AllocResHeap
  (AllocResHeap (HeapCtor (+ 1 (HeapSize h))
                    (store (HeapContents h) (+ 1 (HeapSize h)) o))
          (+ 1 (HeapSize h))))

;===============================================================================
(declare-fun inv_main15 (Heap Int Int Addr) Bool)
(declare-fun inv_main19 (Heap Int Int Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Int Int Addr Addr Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Int Int Int) Bool)
(declare-fun inv_main36 (Heap Int Addr Int Int) Bool)
(declare-fun inv_main42 (Heap Int Addr Int Int Int Int Int) Bool)
(declare-fun inv_main47 (Heap Int Addr Int Int Int) Bool)
(declare-fun inv_main56 (Heap Int Addr Int Int Int Int Int Addr Int) Bool)
(declare-fun inv_main6 (Heap Int Int Int) Bool)
(declare-fun inv_main61 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main63 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Int Addr Int Int Int Int Int Addr Addr Addr) Bool)
(declare-fun inv_main77 (Heap Int Addr Int Int Addr Int) Bool)
(declare-fun inv_main83 (Heap Int Addr Int Int Addr) Bool)
(declare-fun inv_main86 (Heap Int Addr Int Int) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int)) (or (not (and (inv_main42 var1 var7 var5 var6 var2 var4 var3 var0) (not (<= 0 (+ (+ var3 (* (- 1) var0)) (- 1)))))) (inv_main47 var1 var7 var5 var6 var2 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int)) (or (not (and (inv_main42 var1 var8 var5 var7 var2 var4 var3 var0) (and (= var6 0) (<= 0 (+ (+ var3 (* (- 1) var0)) (- 1)))))) (inv_main47 var1 var8 var5 var7 var2 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Int)) (or (not (inv_main56 var1 var8 var5 var7 var3 var0 var6 var9 var2 var4)) (inv_main56 var1 var8 var5 var7 var3 var0 var6 var9 var2 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Heap) (var10 Int) (var11 node) (var12 Int) (var13 Addr) (var14 Int) (var15 Heap)) (or (not (and (inv_main47 var9 var8 var13 var14 var3 var1) (and (= nullAddr var2) (and (and (and (and (and (and (and (and (= var15 (newHeap (alloc var9 (O_node var11)))) (= var4 var8)) (= var6 var13)) (= var12 var14)) (= var0 var3)) (= var5 var1)) (= var7 2)) (= var10 var1)) (= var2 (newAddr (alloc var9 (O_node var11)))))))) (inv_main56 var15 var4 var6 var12 var0 var5 var7 var10 var2 1))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main6 var2 var0 var1 var4) (and (not (= var3 0)) (<= 0 (+ (+ var1 (* (- 1) var4)) (- 1)))))) (inv_main6 var2 var0 var1 (+ var4 1)))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main6 var0 2 5 2))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (or (not (and (inv_main30 var0 var6 var3 var5 var1 var4) (and (not (= var2 0)) (<= 0 (+ (+ var1 (* (- 1) var4)) (- 1)))))) (inv_main30 var0 var6 var3 var5 var1 (+ var4 1)))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int)) (or (not (and (inv_main15 var0 var3 var2 var1) (not (<= 0 (+ var2 (- 1)))))) (inv_main30 var0 var3 var1 0 (+ var3 (- 1)) 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Int) (var17 Int) (var18 Int)) (or (not (and (inv_main66 var12 var10 var15 var17 var5 var0 var16 var18 var13 var3 var1) (and (and (and (and (and (and (and (= var2 (write var12 var3 (O_node (node var13)))) (= var4 var10)) (= var7 var15)) (= var9 var17)) (= var6 var5)) (= var14 var0)) (= var11 var16)) (= var8 var18)))) (inv_main36 var2 var4 var7 var9 (+ var6 1)))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Int) (var17 Int) (var18 Addr) (var19 Int) (var20 Int) (var21 Int)) (or (not (and (inv_main61 var12 var8 var18 var20 var6 var1 var19 var21 var14 var5 var2) (and (= var11 nullAddr) (and (and (and (and (and (and (and (and (and (and (= var15 (write var12 var14 (O_node (node var2)))) (= var17 var8)) (= var10 var18)) (= var0 var20)) (= var16 var6)) (= var7 var1)) (= var4 var19)) (= var3 var21)) (= var13 var14)) (= var11 var5)) (= var9 var2))))) (inv_main36 var15 var17 var13 var0 (+ var16 1)))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main30 var0 var5 var2 var4 var1 var3) (not (<= 0 (+ (+ var1 (* (- 1) var3)) (- 1)))))) (inv_main36 var0 var5 var2 var3 0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Int)) (or (not (and (inv_main30 var1 var6 var3 var5 var2 var4) (and (= var0 0) (<= 0 (+ (+ var2 (* (- 1) var4)) (- 1)))))) (inv_main36 var1 var6 var3 var4 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int)) (or (not (and (inv_main63 var12 var9 var17 var19 var4 var0 var18 var22 var15 var2 var1) (and (not (<= 0 (+ var10 (- 1)))) (and (and (and (and (and (and (and (and (and (and (and (= var16 var12) (= var8 var9)) (= var5 var17)) (= var11 var19)) (= var3 var4)) (= var14 var0)) (= var6 var18)) (= var10 var22)) (= var21 var15)) (= var20 var2)) (= var13 var1)) (= var7 (next (getnode (read var12 var1)))))))) (inv_main61 var16 var8 var5 var11 var3 var14 var6 (+ var10 (- 1)) var21 var20 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 node) (var14 Int) (var15 Addr) (var16 Int) (var17 Heap) (var18 Int) (var19 Addr) (var20 Int) (var21 Int) (var22 Int) (var23 Int) (var24 Int) (var25 Addr)) (or (not (and (inv_main47 var17 var14 var19 var22 var8 var1) (and (and (not (<= 0 (+ var16 (- 1)))) (and (and (and (and (and (and (and (and (and (= var5 var12) (= var6 var7)) (= var15 var9)) (= var21 var3)) (= var0 var10)) (= var18 var20)) (= var2 var24)) (= var16 var23)) (= var11 var4)) (= var25 nullAddr))) (and (not (= nullAddr var4)) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var17 (O_node var13)))) (= var7 var14)) (= var9 var19)) (= var3 var22)) (= var10 var8)) (= var20 var1)) (= var24 2)) (= var23 var1)) (= var4 (newAddr (alloc var17 (O_node var13))))))))) (inv_main61 var5 var6 var15 var21 var0 var18 var2 (+ var16 (- 1)) var11 var25 var15))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Int) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Int) (var21 Int)) (or (not (and (inv_main61 var12 var11 var15 var18 var5 var1 var17 var21 var14 var4 var2) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (and (and (and (and (= var0 (write var12 var14 (O_node (node var2)))) (= var19 var11)) (= var10 var15)) (= var7 var18)) (= var20 var5)) (= var9 var1)) (= var13 var17)) (= var8 var21)) (= var3 var14)) (= var6 var4)) (= var16 var2))))) (inv_main66 var0 var19 var10 var7 var20 var9 var13 var8 var3 var6 var16))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int)) (or (not (and (inv_main83 var8 var6 var17 var18 var4 var16) (and (not (= var15 nullAddr)) (and (and (and (and (and (and (and (= var14 var8) (= var13 var6)) (= var9 var17)) (= var0 var18)) (= var11 var4)) (= var7 var16)) (= var5 (next (getnode (read var8 var16))))) (and (and (and (and (and (and (= var2 (write var14 var7 defObj)) (= var19 var13)) (= var12 var9)) (= var1 var0)) (= var3 var11)) (= var10 var7)) (= var15 var5)))))) (inv_main83 var2 var19 var12 var1 var3 var15))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main77 var9 var8 var12 var14 var4 var5 var3) (and (not (= var11 nullAddr)) (and (= (+ var7 var1) var6) (and (= var2 nullAddr) (and (and (and (and (and (and (and (= var0 var9) (= var1 var8)) (= var11 var12)) (= var7 var14)) (= var13 var4)) (= var10 var5)) (= var6 var3)) (= var2 (next (getnode (read var9 var5)))))))))) (inv_main83 var0 var1 var11 var7 var13 var11))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main36 var0 var4 var2 var3 var1) (and (not (= var2 nullAddr)) (and (and (= (+ var3 var4) 0) (= var2 nullAddr)) (not (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1)))))))) (inv_main83 var0 var4 var2 var3 var1 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Int)) (or (not (and (inv_main42 var2 var8 var6 var7 var3 var5 var4 var1) (and (not (= var0 0)) (<= 0 (+ (+ var4 (* (- 1) var1)) (- 1)))))) (inv_main42 var2 var8 var6 var7 var3 var5 var4 (+ var1 1)))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main36 var0 var4 var2 var3 var1) (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1))))) (inv_main42 var0 var4 var2 var3 var1 0 (+ var1 (+ var4 (- 1))) 0))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main77 var9 var8 var12 var14 var4 var5 var3) (and (not (= (+ var7 var1) var6)) (and (= var2 nullAddr) (and (and (and (and (and (and (and (= var0 var9) (= var1 var8)) (= var11 var12)) (= var7 var14)) (= var13 var4)) (= var10 var5)) (= var6 var3)) (= var2 (next (getnode (read var9 var5))))))))) (inv_main86 var0 var1 var11 var7 var13))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main36 var0 var4 var2 var3 var1) (and (and (not (= (+ var3 var4) 0)) (= var2 nullAddr)) (not (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1))))))) (inv_main86 var0 var4 var2 var3 var1))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 node) (var8 Heap) (var9 Int)) (or (not (and (inv_main15 var2 var9 var4 var3) (and (and (not (= nullAddr var6)) (and (and (and (and (= var8 (newHeap (alloc var2 (O_node var7)))) (= var1 var9)) (= var5 (+ var4 (- 1)))) (= var0 var3)) (= var6 (newAddr (alloc var2 (O_node var7)))))) (<= 0 (+ var4 (- 1)))))) (inv_main19 var8 var1 var5 var0 var6))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int)) (or (not (and (inv_main77 var9 var8 var12 var14 var4 var5 var3) (and (not (= var2 nullAddr)) (and (and (and (and (and (and (and (= var0 var9) (= var1 var8)) (= var11 var12)) (= var7 var14)) (= var13 var4)) (= var10 var5)) (= var6 var3)) (= var2 (next (getnode (read var9 var5)))))))) (inv_main77 var0 var1 var11 var7 var13 var2 (+ var6 1)))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int)) (or (not (and (inv_main36 var0 var4 var2 var3 var1) (and (not (= var2 nullAddr)) (not (<= 0 (+ (+ var3 (* (- 1) var1)) (- 1))))))) (inv_main77 var0 var4 var2 var3 var1 var2 1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (inv_main19 var1 var9 var3 var2 var5) (and (and (and (and (= var8 (write var1 var5 (O_node (node var2)))) (= var6 var9)) (= var0 var3)) (= var4 var2)) (= var7 var5)))) (inv_main15 var8 var6 var0 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int)) (or (not (and (inv_main6 var2 var0 var1 var3) (not (<= 0 (+ (+ var1 (* (- 1) var3)) (- 1)))))) (inv_main15 var2 var3 var3 nullAddr))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Int) (var4 Int)) (or (not (and (inv_main6 var2 var0 var1 var3) (and (= var4 0) (<= 0 (+ (+ var1 (* (- 1) var3)) (- 1)))))) (inv_main15 var2 var3 var3 nullAddr))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Int) (var11 Int) (var12 Heap) (var13 Addr) (var14 Int) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Int)) (or (not (and (inv_main63 var12 var9 var17 var19 var4 var0 var18 var22 var15 var2 var1) (and (<= 0 (+ var10 (- 1))) (and (and (and (and (and (and (and (and (and (and (and (= var16 var12) (= var8 var9)) (= var5 var17)) (= var11 var19)) (= var3 var4)) (= var14 var0)) (= var6 var18)) (= var10 var22)) (= var21 var15)) (= var20 var2)) (= var13 var1)) (= var7 (next (getnode (read var12 var1)))))))) (inv_main63 var16 var8 var5 var11 var3 var14 var6 (+ var10 (- 1)) var21 var7 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 node) (var5 Int) (var6 Int) (var7 Int) (var8 Int) (var9 Heap) (var10 Heap) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr)) (or (not (and (inv_main47 var15 var12 var20 var24 var5 var0) (and (and (<= 0 (+ var17 (- 1))) (and (and (and (and (and (and (and (and (and (= var10 var9) (= var7 var2)) (= var25 var23)) (= var19 var1)) (= var6 var21)) (= var8 var18)) (= var14 var13)) (= var17 var3)) (= var16 var11)) (= var22 nullAddr))) (and (not (= nullAddr var11)) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var15 (O_node var4)))) (= var2 var12)) (= var23 var20)) (= var1 var24)) (= var21 var5)) (= var18 var0)) (= var13 2)) (= var3 var0)) (= var11 (newAddr (alloc var15 (O_node var4))))))))) (inv_main63 var10 var7 var25 var19 var6 var8 var14 (+ var17 (- 1)) var16 var25 var25))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int)) (or (not (inv_main22 var0 var5 var2 var1 var3 var4)) (inv_main22 var0 var5 var2 var1 var3 var4))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr) (var4 node) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (inv_main15 var2 var9 var5 var3) (and (and (= nullAddr var0) (and (and (and (and (= var8 (newHeap (alloc var2 (O_node var4)))) (= var6 var9)) (= var1 (+ var5 (- 1)))) (= var7 var3)) (= var0 (newAddr (alloc var2 (O_node var4)))))) (<= 0 (+ var5 (- 1)))))) (inv_main22 var8 var6 var1 var7 var0 1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int)) (not (and (inv_main19 var0 var4 var2 var1 var3) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (not (and (inv_main63 var2 var9 var6 var8 var5 var0 var7 var10 var4 var3 var1) (not (is-O_node (read var2 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (not (and (inv_main61 var2 var9 var6 var8 var5 var0 var7 var10 var4 var3 var1) (not (is-O_node (read var2 var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Int) (var9 Int) (var10 Int)) (not (and (inv_main66 var2 var9 var6 var8 var5 var0 var7 var10 var4 var3 var1) (not (is-O_node (read var2 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Int)) (not (and (inv_main77 var0 var6 var4 var5 var2 var3 var1) (not (is-O_node (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Int)) (not (and (inv_main83 var0 var5 var3 var4 var1 var2) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Int) (var4 Int)) (not (inv_main86 var0 var4 var2 var3 var1))))
(check-sat)
