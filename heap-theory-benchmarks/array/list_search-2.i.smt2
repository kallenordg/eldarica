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
(declare-datatypes ((HeapObject 0) (list 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_list (getlist list)) (defObj))
                   ((list (key Int) (next Addr)))))
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
(declare-fun inv_main100 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main13 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main14 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main16 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main27 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main28 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main30 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main32 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main41 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main42 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main44 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main46 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main5 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main55 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main56 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main58 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Int Addr Int Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main62 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main65 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main67 (Heap Int Addr Int Addr Addr) Bool)
(declare-fun inv_main71 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main74 (Heap Int Addr Int Addr Addr Addr Int) Bool)
(declare-fun inv_main86 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main87 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main88 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main90 (Heap Int Addr Int Addr Addr Addr Addr) Bool)
(declare-fun inv_main95 (Heap Int Addr Int Addr Addr Addr Addr Addr) Bool)
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int)) (or (not (and (and (= var2 emptyHeap) (= var5 0)) (= var4 var0))) (inv_main5 var2 var5 var4 var3 0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 list) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Int)) (or (not (and (inv_main30 var15 var18 var6 var3 var21 var1 var23 var20) (and (and (= var5 nullAddr) (and (and (and (and (and (and (and (and (= var11 (newHeap (alloc var7 (O_list var2)))) (= var25 var4)) (= var5 var16)) (= var24 var8)) (= var22 var10)) (= var13 var0)) (= var19 var10)) (= var17 1)) (= var9 (newAddr (alloc var7 (O_list var2)))))) (and (and (and (and (and (and (and (= var7 (write var15 var23 (O_list (list (key (getlist (read var15 var23))) nullAddr)))) (= var4 var18)) (= var14 var6)) (= var8 var3)) (= var10 var21)) (= var0 var1)) (= var16 var23)) (= var12 var20))))) (inv_main41 var11 var25 var5 var24 var22 var13 var9 var17))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 list) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Addr)) (or (not (and (inv_main32 var14 var18 var9 var5 var22 var1 var23 var21 var15) (and (and (= var20 nullAddr) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var16 (O_list var6)))) (= var25 var17)) (= var20 var24)) (= var13 var19)) (= var4 var12)) (= var11 var26)) (= var3 var12)) (= var10 1)) (= var7 (newAddr (alloc var16 (O_list var6)))))) (and (and (and (and (and (and (and (= var16 (write var14 var23 (O_list (list (key (getlist (read var14 var23))) var15)))) (= var17 var18)) (= var2 var9)) (= var19 var5)) (= var12 var22)) (= var26 var1)) (= var24 var23)) (= var0 var21))))) (inv_main41 var8 var25 var20 var13 var4 var11 var7 var10))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 list)) (or (not (and (inv_main16 var14 var19 var7 var5 var22 var1 var16 var8) (and (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (and (= var11 (newHeap (alloc var4 (O_list var25)))) (= var24 var2)) (= var12 var10)) (= var0 var13)) (= var21 var6)) (= var15 var3)) (= var9 var6)) (= var23 5)) (= var18 (newAddr (alloc var4 (O_list var25)))))) (and (and (and (and (and (and (and (= var4 (write var14 var16 (O_list (list (key (getlist (read var14 var16))) nullAddr)))) (= var2 var19)) (= var17 var7)) (= var13 var5)) (= var6 var22)) (= var3 var1)) (= var10 var16)) (= var20 var8))))) (inv_main28 var11 var24 var12 var0 var21 var15 var18 var23))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Heap) (var4 list) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Addr) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Int) (var26 Heap)) (or (not (and (inv_main18 var16 var19 var7 var2 var23 var1 var18 var9 var14) (and (and (not (= var12 nullAddr)) (and (and (and (and (and (and (and (and (= var26 (newHeap (alloc var3 (O_list var4)))) (= var24 var6)) (= var12 var0)) (= var8 var20)) (= var21 var17)) (= var11 var15)) (= var13 var17)) (= var5 5)) (= var22 (newAddr (alloc var3 (O_list var4)))))) (and (and (and (and (and (and (and (= var3 (write var16 var18 (O_list (list (key (getlist (read var16 var18))) var14)))) (= var6 var19)) (= var10 var7)) (= var20 var2)) (= var17 var23)) (= var15 var1)) (= var0 var18)) (= var25 var9))))) (inv_main28 var26 var24 var12 var8 var21 var11 var22 var5))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Addr) (var8 list) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Int) (var15 Int) (var16 Int) (var17 Int) (var18 Addr) (var19 Addr) (var20 Addr) (var21 Addr) (var22 Int) (var23 Heap) (var24 Addr) (var25 Addr)) (or (not (and (inv_main44 var13 var16 var6 var4 var20 var0 var11 var9) (and (and (= var24 nullAddr) (and (and (and (and (and (and (and (and (= var23 (newHeap (alloc var2 (O_list var8)))) (= var5 var15)) (= var24 var19)) (= var22 var1)) (= var12 var3)) (= var7 var18)) (= var10 var3)) (= var17 3)) (= var25 (newAddr (alloc var2 (O_list var8)))))) (and (and (and (and (and (and (and (= var2 (write var13 var11 (O_list (list (key (getlist (read var13 var11))) nullAddr)))) (= var15 var16)) (= var21 var6)) (= var1 var4)) (= var3 var20)) (= var18 var0)) (= var19 var11)) (= var14 var9))))) (inv_main55 var23 var5 var24 var22 var12 var7 var25 var17))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Int) (var10 Addr) (var11 list) (var12 Heap) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Addr) (var26 Int)) (or (not (and (inv_main46 var12 var18 var4 var2 var21 var0 var10 var7 var3) (and (and (= var22 nullAddr) (and (and (and (and (and (and (and (and (= var16 (newHeap (alloc var6 (O_list var11)))) (= var17 var26)) (= var22 var25)) (= var19 var23)) (= var15 var20)) (= var8 var14)) (= var13 var20)) (= var1 3)) (= var24 (newAddr (alloc var6 (O_list var11)))))) (and (and (and (and (and (and (and (= var6 (write var12 var10 (O_list (list (key (getlist (read var12 var10))) var3)))) (= var26 var18)) (= var5 var4)) (= var23 var2)) (= var20 var21)) (= var14 var0)) (= var25 var10)) (= var9 var7))))) (inv_main55 var16 var17 var22 var19 var15 var8 var24 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr)) (or (not (inv_main27 var1 var3 var4 var2 var6 var0 var7 var5)) (inv_main30 (write var1 var7 (O_list (list var5 (next (getlist (read var1 var7)))))) var3 var4 var2 var6 var0 var7 var5))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main87 var11 var13 var6 var5 var14 var0 var7 var4) (and (= var3 var10) (and (and (and (and (and (and (and (and (= var16 var11) (= var2 var13)) (= var8 var6)) (= var9 var5)) (= var12 var14)) (= var15 var0)) (= var10 var7)) (= var1 var4)) (= var3 (next (getlist (read var11 var4)))))))) (inv_main86 var16 var2 var8 var9 var12 var15 var10 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main88 var12 var13 var7 var5 var14 var2 var8 var4) (and (and (and (and (and (and (and (and (= var0 var12) (= var9 var13)) (= var15 var7)) (= var1 var5)) (= var10 var14)) (= var16 var2)) (= var6 var8)) (= var3 var4)) (= var11 (next (getlist (read var12 var8))))))) (inv_main86 var0 var9 var11 var1 var10 var16 var6 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (inv_main55 var1 var4 var5 var3 var7 var0 var2 var6)) (inv_main58 (write var1 var2 (O_list (list var6 (next (getlist (read var1 var2)))))) var4 var5 var3 var7 var0 var2 var6))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 list) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (inv_main5 var12 var13 var6 var5 var15 var2) (and (not (= var9 nullAddr)) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var12 (O_list var11)))) (= var7 var13)) (= var9 var6)) (= var1 var5)) (= var4 var15)) (= var3 var2)) (= var14 var15)) (= var0 2)) (= var10 (newAddr (alloc var12 (O_list var11)))))))) (inv_main14 var8 var7 var9 var1 var4 var3 var10 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Int) (var14 Heap) (var15 Addr) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Heap) (var21 Addr) (var22 Addr) (var23 Int) (var24 Addr) (var25 Addr)) (or (not (and (inv_main71 var14 var19 var4 var2 var21 var1 var6 var11) (and (and (not (= var16 0)) (and (not (= var6 nullAddr)) (and (and (and (and (and (and (and (and (= var20 var14) (= var18 var19)) (= var9 var4)) (= var7 var2)) (= var10 var21)) (= var24 var1)) (= var17 var6)) (= var13 var11)) (= var23 (key (getlist (read var14 var6))))))) (and (and (and (and (and (and (and (and (= var3 var20) (= var8 var18)) (= var22 var9)) (= var12 var7)) (= var25 var10)) (= var5 var24)) (= var15 var17)) (= var0 var13)) (or (and (not (= var23 var13)) (= var16 1)) (and (= var23 var13) (= var16 0))))))) (inv_main74 var3 var8 var22 var12 var25 var5 var15 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int)) (or (not (and (inv_main74 var9 var11 var6 var3 var12 var1 var7 var8) (and (and (and (and (and (and (and (and (= var0 var9) (= var2 var11)) (= var13 var6)) (= var5 var3)) (= var4 var12)) (= var14 var1)) (= var15 var7)) (= var16 var8)) (= var10 (next (getlist (read var9 var7))))))) (inv_main71 var0 var2 var13 var5 var4 var14 var10 var16))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (inv_main62 var1 var3 var4 var2 var5 var0) (= var5 nullAddr))) (inv_main71 var1 var3 var4 var2 var5 var0 var4 2))))
(assert (forall ((var0 Addr) (var1 list) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Heap) (var12 Int) (var13 Int) (var14 Addr) (var15 Int) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Heap)) (or (not (and (inv_main30 var17 var19 var9 var5 var22 var2 var23 var21) (and (and (not (= var10 nullAddr)) (and (and (and (and (and (and (and (and (= var25 (newHeap (alloc var11 (O_list var1)))) (= var15 var8)) (= var10 var18)) (= var3 var12)) (= var20 var14)) (= var4 var0)) (= var24 var14)) (= var6 1)) (= var7 (newAddr (alloc var11 (O_list var1)))))) (and (and (and (and (and (and (and (= var11 (write var17 var23 (O_list (list (key (getlist (read var17 var23))) nullAddr)))) (= var8 var19)) (= var16 var9)) (= var12 var5)) (= var14 var22)) (= var0 var2)) (= var18 var23)) (= var13 var21))))) (inv_main42 var25 var15 var10 var3 var20 var4 var7 var6))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Heap) (var12 Addr) (var13 Heap) (var14 Int) (var15 list) (var16 Int) (var17 Int) (var18 Int) (var19 Int) (var20 Addr) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Addr)) (or (not (and (inv_main32 var11 var16 var4 var3 var20 var1 var23 var19 var12) (and (and (not (= var6 nullAddr)) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var13 (O_list var15)))) (= var5 var14)) (= var6 var24)) (= var21 var18)) (= var10 var7)) (= var8 var26)) (= var22 var7)) (= var17 1)) (= var25 (newAddr (alloc var13 (O_list var15)))))) (and (and (and (and (and (and (and (= var13 (write var11 var23 (O_list (list (key (getlist (read var11 var23))) var12)))) (= var14 var16)) (= var2 var4)) (= var18 var3)) (= var7 var20)) (= var26 var1)) (= var24 var23)) (= var0 var19))))) (inv_main42 var9 var5 var6 var21 var10 var8 var25 var17))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (inv_main62 var1 var3 var4 var2 var5 var0) (not (= var5 nullAddr)))) (inv_main65 var1 var3 var4 var2 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr)) (or (not (and (inv_main87 var12 var13 var6 var5 var14 var0 var7 var4) (and (not (= var1 var8)) (and (and (and (and (and (and (and (and (= var9 var12) (= var2 var13)) (= var15 var6)) (= var3 var5)) (= var16 var14)) (= var11 var0)) (= var8 var7)) (= var10 var4)) (= var1 (next (getlist (read var12 var4)))))))) (inv_main90 var9 var2 var15 var3 var16 var11 var8 var10))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int)) (or (not (and (inv_main28 var8 var9 var5 var4 var13 var0 var14 var12) (and (and (and (and (and (and (and (= var7 (write var8 var14 (O_list (list var12 (next (getlist (read var8 var14))))))) (= var11 var9)) (= var1 var5)) (= var15 var4)) (= var2 var13)) (= var3 var0)) (= var10 var14)) (= var6 var12)))) (inv_main32 var7 var11 var1 var15 var2 var3 var10 var6 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Int) (var7 Int) (var8 Addr) (var9 Heap) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap) (var18 Int) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 list)) (or (not (and (inv_main44 var17 var20 var8 var6 var23 var2 var15 var12) (and (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (and (= var9 (newHeap (alloc var4 (O_list var25)))) (= var16 var19)) (= var13 var22)) (= var7 var3)) (= var11 var5)) (= var14 var21)) (= var1 var5)) (= var10 3)) (= var0 (newAddr (alloc var4 (O_list var25)))))) (and (and (and (and (and (and (and (= var4 (write var17 var15 (O_list (list (key (getlist (read var17 var15))) nullAddr)))) (= var19 var20)) (= var24 var8)) (= var3 var6)) (= var5 var23)) (= var21 var2)) (= var22 var15)) (= var18 var12))))) (inv_main56 var9 var16 var13 var7 var11 var14 var0 var10))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap) (var9 Int) (var10 Heap) (var11 list) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Int) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Int) (var25 Addr) (var26 Int)) (or (not (and (inv_main46 var15 var18 var6 var4 var21 var0 var14 var9 var5) (and (and (not (= var13 nullAddr)) (and (and (and (and (and (and (and (and (= var10 (newHeap (alloc var8 (O_list var11)))) (= var1 var26)) (= var13 var25)) (= var16 var24)) (= var22 var20)) (= var23 var17)) (= var3 var20)) (= var19 3)) (= var2 (newAddr (alloc var8 (O_list var11)))))) (and (and (and (and (and (and (and (= var8 (write var15 var14 (O_list (list (key (getlist (read var15 var14))) var5)))) (= var26 var18)) (= var7 var6)) (= var24 var4)) (= var20 var21)) (= var17 var0)) (= var25 var14)) (= var12 var9))))) (inv_main56 var10 var1 var13 var16 var22 var23 var2 var19))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (and (inv_main71 var1 var3 var4 var2 var5 var0 var6 var7) (= var6 nullAddr))) (inv_main67 var1 var3 var4 var2 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Addr) (var6 Int) (var7 Heap) (var8 Addr) (var9 Int) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Int) (var21 Heap) (var22 Addr) (var23 Int) (var24 Int) (var25 Addr)) (or (not (and (inv_main71 var15 var19 var4 var3 var22 var1 var5 var12) (and (and (= var23 0) (and (not (= var5 nullAddr)) (and (and (and (and (and (and (and (and (= var21 var15) (= var18 var19)) (= var10 var4)) (= var6 var3)) (= var11 var22)) (= var25 var1)) (= var17 var5)) (= var14 var12)) (= var24 (key (getlist (read var15 var5))))))) (and (and (and (and (and (and (and (and (= var7 var21) (= var13 var18)) (= var8 var10)) (= var9 var6)) (= var0 var11)) (= var2 var25)) (= var16 var17)) (= var20 var14)) (or (and (not (= var24 var14)) (= var23 1)) (and (= var24 var14) (= var23 0))))))) (inv_main67 var7 var13 var8 var9 var0 var16))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Heap) (var13 Int) (var14 Addr) (var15 Heap) (var16 Addr) (var17 list) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Int) (var24 Int) (var25 Int)) (or (not (and (inv_main16 var15 var19 var7 var4 var22 var0 var16 var8) (and (and (= var14 nullAddr) (and (and (and (and (and (and (and (and (= var12 (newHeap (alloc var3 (O_list var17)))) (= var24 var1)) (= var14 var11)) (= var23 var13)) (= var5 var6)) (= var10 var2)) (= var9 var6)) (= var25 5)) (= var21 (newAddr (alloc var3 (O_list var17)))))) (and (and (and (and (and (and (and (= var3 (write var15 var16 (O_list (list (key (getlist (read var15 var16))) nullAddr)))) (= var1 var19)) (= var18 var7)) (= var13 var4)) (= var6 var22)) (= var2 var0)) (= var11 var16)) (= var20 var8))))) (inv_main27 var12 var24 var14 var23 var5 var10 var21 var25))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 list) (var3 Int) (var4 Int) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Addr) (var20 Int) (var21 Int) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Int) (var26 Int)) (or (not (and (inv_main18 var17 var20 var8 var4 var24 var1 var19 var10 var14) (and (and (= var6 nullAddr) (and (and (and (and (and (and (and (and (= var13 (newHeap (alloc var5 (O_list var2)))) (= var9 var7)) (= var6 var0)) (= var26 var21)) (= var23 var18)) (= var22 var16)) (= var12 var18)) (= var3 5)) (= var15 (newAddr (alloc var5 (O_list var2)))))) (and (and (and (and (and (and (and (= var5 (write var17 var19 (O_list (list (key (getlist (read var17 var19))) var14)))) (= var7 var20)) (= var11 var8)) (= var21 var4)) (= var18 var24)) (= var16 var1)) (= var0 var19)) (= var25 var10))))) (inv_main27 var13 var9 var6 var26 var23 var22 var15 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int)) (or (not (and (inv_main100 var3 var7 var8 var4 var9 var2) (and (not (= var5 nullAddr)) (and (and (and (and (and (and (= var1 var3) (= var12 var7)) (= var6 var8)) (= var10 var4)) (= var11 var9)) (= var0 var2)) (= var5 (next (getlist (read var3 var9)))))))) (inv_main100 var1 var12 var6 var10 var5 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Int) (var15 Heap) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr)) (or (not (and (inv_main95 var17 var20 var5 var4 var21 var0 var6 var3 var10) (and (not (= var16 nullAddr)) (and (and (and (and (and (and (and (and (= var9 (write var17 var3 (O_list (list (key (getlist (read var17 var3))) var10)))) (= var13 var20)) (= var23 var5)) (= var2 var4)) (= var11 var21)) (= var8 var0)) (= var24 var6)) (= var18 var3)) (and (and (and (and (and (and (and (= var15 (write var9 var24 defObj)) (= var14 var13)) (= var16 var23)) (= var19 var2)) (= var22 var11)) (= var1 var8)) (= var12 var24)) (= var7 var18)))))) (inv_main100 var15 var14 var16 var19 var16 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int)) (or (not (inv_main41 var2 var4 var5 var3 var6 var0 var1 var7)) (inv_main44 (write var2 var1 (O_list (list var7 (next (getlist (read var2 var1)))))) var4 var5 var3 var6 var0 var1 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Heap)) (or (not (and (inv_main90 var7 var9 var4 var2 var12 var0 var5 var1) (and (and (and (and (and (and (and (and (= var16 var7) (= var13 var9)) (= var3 var4)) (= var10 var2)) (= var11 var12)) (= var6 var0)) (= var14 var5)) (= var8 var1)) (= var15 (next (getlist (read var7 var1))))))) (inv_main87 var16 var13 var3 var10 var11 var6 var14 var15))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (inv_main67 var1 var3 var4 var2 var5 var0) (not (= var4 var0)))) (inv_main87 var1 var3 var4 var2 var5 var0 var0 var4))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Int) (var8 Heap) (var9 Addr) (var10 Addr) (var11 list) (var12 Heap) (var13 Int) (var14 Addr) (var15 Addr)) (or (not (and (inv_main5 var12 var13 var6 var5 var15 var2) (and (= var9 nullAddr) (and (and (and (and (and (and (and (and (= var8 (newHeap (alloc var12 (O_list var11)))) (= var7 var13)) (= var9 var6)) (= var1 var5)) (= var4 var15)) (= var3 var2)) (= var14 var15)) (= var0 2)) (= var10 (newAddr (alloc var12 (O_list var11)))))))) (inv_main13 var8 var7 var9 var1 var4 var3 var10 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Heap) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr)) (or (not (and (inv_main42 var9 var12 var3 var2 var14 var0 var7 var4) (and (and (and (and (and (and (and (= var6 (write var9 var7 (O_list (list var4 (next (getlist (read var9 var7))))))) (= var5 var12)) (= var15 var3)) (= var8 var2)) (= var13 var14)) (= var10 var0)) (= var1 var7)) (= var11 var4)))) (inv_main46 var6 var5 var15 var8 var13 var10 var1 var11 var15))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Int) (var14 Heap) (var15 Addr)) (or (not (and (inv_main14 var7 var10 var3 var2 var11 var0 var8 var4) (and (and (and (and (and (and (and (= var14 (write var7 var8 (O_list (list var4 (next (getlist (read var7 var8))))))) (= var1 var10)) (= var6 var3)) (= var5 var2)) (= var15 var11)) (= var12 var0)) (= var9 var8)) (= var13 var4)))) (inv_main18 var14 var1 var6 var5 var15 var12 var9 var13 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (or (not (and (inv_main67 var1 var3 var4 var2 var5 var0) (= var4 var0))) (inv_main88 var1 var3 var4 var2 var5 var0 var0 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (inv_main86 var1 var4 var5 var3 var7 var0 var6 var2)) (inv_main95 var1 var4 var5 var3 var7 var0 var6 var2 (next (getlist (read var1 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (or (not (inv_main13 var1 var4 var5 var3 var7 var0 var2 var6)) (inv_main16 (write var1 var2 (O_list (list var6 (next (getlist (read var1 var2)))))) var4 var5 var3 var7 var0 var2 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Addr)) (or (not (and (inv_main65 var1 var5 var6 var2 var7 var0) (and (and (and (and (and (and (= var11 var1) (= var8 var5)) (= var12 var6)) (= var9 var2)) (= var4 var7)) (= var3 var0)) (= var10 (next (getlist (read var1 var7))))))) (inv_main62 var11 var8 var12 var9 var10 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Addr) (var5 Int) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int)) (or (not (and (inv_main58 var8 var10 var4 var3 var13 var0 var9 var12) (and (and (and (and (and (and (and (= var1 (write var8 var9 (O_list (list (key (getlist (read var8 var9))) nullAddr)))) (= var15 var10)) (= var7 var4)) (= var6 var3)) (= var2 var13)) (= var11 var0)) (= var14 var9)) (= var5 var12)))) (inv_main62 var1 var15 var14 var6 var14 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Heap) (var13 Addr) (var14 Int) (var15 Int) (var16 Addr)) (or (not (and (inv_main60 var12 var14 var8 var6 var16 var2 var13 var15 var9) (and (and (and (and (and (and (and (= var5 (write var12 var13 (O_list (list (key (getlist (read var12 var13))) var9)))) (= var10 var14)) (= var1 var8)) (= var7 var6)) (= var0 var16)) (= var11 var2)) (= var4 var13)) (= var3 var15)))) (inv_main62 var5 var10 var4 var7 var4 var11))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Int) (var13 Int) (var14 Int) (var15 Addr)) (or (not (and (inv_main56 var9 var12 var5 var3 var15 var1 var10 var14) (and (and (and (and (and (and (and (= var0 (write var9 var10 (O_list (list var14 (next (getlist (read var9 var10))))))) (= var13 var12)) (= var2 var5)) (= var7 var3)) (= var6 var15)) (= var11 var1)) (= var8 var10)) (= var4 var14)))) (inv_main60 var0 var13 var2 var7 var6 var11 var8 var4 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main13 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main16 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main14 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Int) (var6 Addr) (var7 Int) (var8 Addr)) (not (and (inv_main18 var2 var5 var6 var4 var8 var1 var3 var7 var0) (not (is-O_list (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr)) (not (and (inv_main27 var1 var3 var4 var2 var6 var0 var7 var5) (not (is-O_list (read var1 var7)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr)) (not (and (inv_main30 var1 var3 var4 var2 var6 var0 var7 var5) (not (is-O_list (read var1 var7)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr)) (not (and (inv_main28 var1 var3 var4 var2 var6 var0 var7 var5) (not (is-O_list (read var1 var7)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main32 var1 var4 var5 var3 var7 var0 var8 var6 var2) (not (is-O_list (read var1 var8)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int)) (not (and (inv_main41 var2 var4 var5 var3 var6 var0 var1 var7) (not (is-O_list (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int)) (not (and (inv_main44 var2 var4 var5 var3 var6 var0 var1 var7) (not (is-O_list (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Int)) (not (and (inv_main42 var2 var4 var5 var3 var6 var0 var1 var7) (not (is-O_list (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Int) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int)) (not (and (inv_main46 var2 var5 var6 var3 var7 var0 var1 var8 var4) (not (is-O_list (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main55 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main58 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr)) (not (and (inv_main56 var1 var4 var5 var3 var7 var0 var2 var6) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Int) (var7 Addr) (var8 Addr)) (not (and (inv_main60 var1 var4 var5 var3 var8 var0 var2 var6 var7) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (not (and (inv_main65 var1 var3 var4 var2 var5 var0) (not (is-O_list (read var1 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (not (and (inv_main71 var1 var3 var4 var2 var5 var0 var6 var7) (and (not (= var6 nullAddr)) (not (is-O_list (read var1 var6))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int)) (not (and (inv_main74 var1 var3 var4 var2 var5 var0 var6 var7) (not (is-O_list (read var1 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (not (and (inv_main67 var1 var3 var4 var2 var5 var0) (not (is-O_list (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (not (and (inv_main67 var1 var3 var4 var2 var5 var0) (not (= (key (getlist (read var1 var0))) 2))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main87 var1 var4 var5 var3 var7 var0 var6 var2) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main90 var1 var4 var5 var3 var7 var0 var6 var2) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main88 var1 var4 var5 var3 var7 var0 var6 var2) (not (is-O_list (read var1 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr)) (not (and (inv_main86 var1 var4 var5 var3 var7 var0 var6 var2) (not (is-O_list (read var1 var6)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Int) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (not (and (inv_main95 var1 var4 var5 var3 var7 var0 var6 var2 var8) (not (is-O_list (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Int) (var4 Addr) (var5 Addr)) (not (and (inv_main100 var1 var3 var4 var2 var5 var0) (not (is-O_list (read var1 var5)))))))
(check-sat)
