(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (TSLL 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_TSLL (getTSLL TSLL)) (defObj))
                   ((TSLL (next Addr) (inner Addr)))))
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
(declare-fun inv_main10 (Heap Addr) Bool)
(declare-fun inv_main103 (Heap Addr Addr) Bool)
(declare-fun inv_main106 (Heap Addr Addr) Bool)
(declare-fun inv_main109 (Heap Addr Addr) Bool)
(declare-fun inv_main11 (Heap Addr) Bool)
(declare-fun inv_main111 (Heap Addr Addr) Bool)
(declare-fun inv_main114 (Heap Addr Addr) Bool)
(declare-fun inv_main116 (Heap Addr Addr) Bool)
(declare-fun inv_main121 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr) Bool)
(declare-fun inv_main15 (Heap Addr Addr) Bool)
(declare-fun inv_main16 (Heap Addr) Bool)
(declare-fun inv_main19 (Heap Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr Addr) Bool)
(declare-fun inv_main26 (Heap Addr Addr) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr) Bool)
(declare-fun inv_main31 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main32 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr) Bool)
(declare-fun inv_main49 (Heap Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main64 (Heap Addr Addr) Bool)
(declare-fun inv_main69 (Heap Addr Addr Int) Bool)
(declare-fun inv_main7 (Heap Addr) Bool)
(declare-fun inv_main70 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main76 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main78 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main81 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main83 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main86 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main88 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main93 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main96 (Heap Addr Addr Int Addr) Bool)
(declare-fun inv_main98 (Heap Addr Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (and (inv_main109 var1 var0 var2) (= nullAddr (inner (getTSLL (read var1 var2)))))) (inv_main114 var1 var0 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main106 var5 var3 var8) (and (not (= nullAddr var1)) (and (and (and (and (= var4 var5) (= var9 var3)) (= var7 var8)) (= var2 (next (getTSLL (read var5 var3))))) (and (and (= var0 (write var4 var9 defObj)) (= var6 var9)) (= var1 var2)))))) (inv_main103 var0 var1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main96 var5 var2 var10 var0 var1) (and (not (= nullAddr var7)) (and (= nullAddr var8) (and (and (and (and (and (= var6 var5) (= var7 var2)) (= var4 var10)) (= var3 var0)) (= var9 var1)) (= var8 (next (getTSLL (read var5 var10))))))))) (inv_main103 var6 var7 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var4 var3 var5) (and (not (= nullAddr var2)) (and (= nullAddr var2) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var6 var4) (= var2 var3)) (= var0 nullAddr)))))))) (inv_main103 var6 var2 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (and (inv_main109 var1 var0 var2) (not (= nullAddr (inner (getTSLL (read var1 var2))))))) (inv_main116 var1 var0 var2))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Int) (var5 Heap)) (or (not (and (inv_main3 var3 var1) (and (= var4 0) (and (not (= var2 nullAddr)) (and (= var5 (write var3 var1 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var3 var1))))))) (= var2 var1)))))) (inv_main15 (newHeap (alloc var5 (O_TSLL var0))) var2 (newAddr (alloc var5 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main45 var1 var0 var2)) (inv_main56 var1 var0 var2 (inner (getTSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var4 var3 var5) (and (= nullAddr var2) (and (= var1 0) (and (and (= var6 var4) (= var2 var3)) (= var0 nullAddr)))))) (inv_main64 var6 var2 var2))))
(assert (forall ((var0 TSLL) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int)) (or (not (and (inv_main26 var2 var1 var3) (not (= var4 0)))) (inv_main31 (newHeap (alloc var2 (O_TSLL var0))) var1 var3 (newAddr (alloc var2 (O_TSLL var0)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main86 var6 var4 var8 var1 var3) (and (= var7 1) (and (and (and (and (and (= var5 var6) (= var10 var4)) (= var9 var8)) (= var7 var1)) (= var2 var3)) (= var0 (inner (getTSLL (read var6 var3)))))))) (inv_main93 var5 var10 var9 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (<= 0 (+ 1 (* (- 1) var0))) (= nullAddr var1)))) (inv_main96 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (= nullAddr var1) (and (= var0 0) (not (= nullAddr var1)))))) (inv_main78 var3 var2 var4 1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (= nullAddr var1) (and (not (= var0 0)) (not (= nullAddr var1)))))) (inv_main78 var3 var2 var4 2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main49 var1 var0 var2)) (inv_main51 (write var1 (inner (getTSLL (read var1 var2))) (O_TSLL (TSLL nullAddr (inner (getTSLL (read var1 (inner (getTSLL (read var1 var2))))))))) var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main103 var1 var0 var4) (and (not (= nullAddr var6)) (and (not (= nullAddr var6)) (and (and (and (= var3 var1) (= var5 var0)) (= var2 var4)) (= var6 (inner (getTSLL (read var1 var0))))))))) (inv_main109 var3 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main10 var1 var0)) (inv_main21 var1 var0 (inner (getTSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main15 var2 var0 var1)) (inv_main14 (write var2 var0 (O_TSLL (TSLL (next (getTSLL (read var2 var0))) var1))) var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main50 var1 var0 var2 var3)) (inv_main49 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) var3))) var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (inv_main56 var1 var0 var3 var2) (not (= var2 nullAddr)))) (inv_main26 var1 var0 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (inv_main56 var5 var2 var8 var7) (and (and (not (= var6 0)) (and (= var7 nullAddr) (and (and (and (= var0 var5) (= var1 var2)) (= var3 var8)) (= var10 (inner (getTSLL (read var5 var8))))))) (and (and (and (= var4 var0) (= var9 var1)) (= var11 var3)) (or (and (= var10 nullAddr) (= var6 1)) (and (not (= var10 nullAddr)) (= var6 0))))))) (inv_main26 var4 var9 var11))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (and (inv_main21 var2 var1 var0) (not (= var0 nullAddr)))) (inv_main26 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Int)) (or (not (and (inv_main21 var4 var2 var0) (and (and (not (= var8 0)) (and (= var0 nullAddr) (and (and (= var7 var4) (= var6 var2)) (= var1 (inner (getTSLL (read var4 var2))))))) (and (and (= var5 var7) (= var3 var6)) (or (and (= var1 nullAddr) (= var8 1)) (and (not (= var1 nullAddr)) (= var8 0))))))) (inv_main26 var5 var3 var3))))
(assert (forall ((var0 Heap) (var1 TSLL)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_TSLL var1))) (newAddr (alloc var0 (O_TSLL var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main30 var3 var0 var5) (and (and (and (= var2 var3) (= var6 var0)) (= var4 var5)) (= var1 (next (getTSLL (read var3 var5))))))) (inv_main32 var2 var6 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Addr)) (or (not (and (inv_main3 var1 var0) (and (= var3 nullAddr) (and (= var2 (write var1 var0 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var1 var0))))))) (= var3 var0))))) (inv_main7 var2 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (not (= nullAddr var1)) (and (= var0 0) (not (= nullAddr var1)))))) (inv_main76 var3 var2 var4 1 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (not (= nullAddr var1)) (and (not (= var0 0)) (not (= nullAddr var1)))))) (inv_main76 var3 var2 var4 2 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap)) (or (not (and (inv_main3 var3 var1) (and (not (= var0 0)) (and (not (= var2 nullAddr)) (and (= var4 (write var3 var1 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var3 var1))))))) (= var2 var1)))))) (inv_main11 var4 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main70 var3 var2 var4 var0 var1) (and (not (<= 0 (+ 1 (* (- 1) var0)))) (= nullAddr var1)))) (inv_main98 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main103 var1 var0 var4) (and (= nullAddr var6) (and (and (and (= var3 var1) (= var5 var0)) (= var2 var4)) (= var6 (inner (getTSLL (read var1 var0)))))))) (inv_main106 var3 var5 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Heap) (var5 Addr)) (or (not (and (inv_main114 var4 var3 var5) (and (= nullAddr (next (getTSLL (read var4 var5)))) (and (and (= var2 (write var4 var5 defObj)) (= var1 var3)) (= var0 var5))))) (inv_main106 var2 var1 nullAddr))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main14 var1 var0)) (inv_main16 (write var1 (inner (getTSLL (read var1 var0))) (O_TSLL (TSLL nullAddr (inner (getTSLL (read var1 (inner (getTSLL (read var1 var0))))))))) var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main81 var3 var2 var4 var0 var1) (= nullAddr (next (getTSLL (read var3 var1)))))) (inv_main86 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (and (inv_main114 var1 var0 var2) (not (= nullAddr (next (getTSLL (read var1 var2))))))) (inv_main121 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main32 var2 var1 var4) (and (= nullAddr var3) (and (and (= var5 (write var2 var4 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var2 var4))))))) (= var0 var1)) (= var3 var4))))) (inv_main37 var5 var0 var3))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main11 var1 var0)) (inv_main10 (write var1 var0 (O_TSLL (TSLL (next (getTSLL (read var1 var0))) nullAddr))) var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main16 var1 var0)) (inv_main10 (write var1 (inner (getTSLL (read var1 var0))) (O_TSLL (TSLL (next (getTSLL (read var1 (inner (getTSLL (read var1 var0)))))) nullAddr))) var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main46 var1 var0 var2)) (inv_main45 (write var1 var2 (O_TSLL (TSLL (next (getTSLL (read var1 var2))) nullAddr))) var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (or (not (inv_main51 var1 var0 var2)) (inv_main45 (write var1 (inner (getTSLL (read var1 var2))) (O_TSLL (TSLL (next (getTSLL (read var1 (inner (getTSLL (read var1 var2)))))) nullAddr))) var0 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Int) (var8 Heap)) (or (not (and (inv_main21 var4 var2 var0) (and (and (= var7 0) (and (= var0 nullAddr) (and (and (= var8 var4) (= var6 var2)) (= var1 (inner (getTSLL (read var4 var2))))))) (and (and (= var5 var8) (= var3 var6)) (or (and (= var1 nullAddr) (= var7 1)) (and (not (= var1 nullAddr)) (= var7 0))))))) (inv_main19 var5 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main32 var3 var1 var5) (and (not (= var0 0)) (and (not (= var4 nullAddr)) (and (not (= nullAddr var4)) (and (and (= var6 (write var3 var5 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var3 var5))))))) (= var2 var1)) (= var4 var5))))))) (inv_main46 var6 var2 var4))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main76 var3 var2 var4 var0 var1) (= nullAddr (inner (getTSLL (read var3 var1)))))) (inv_main81 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap)) (or (not (and (inv_main32 var2 var0 var4) (and (= var3 nullAddr) (and (not (= nullAddr var3)) (and (and (= var5 (write var2 var4 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var2 var4))))))) (= var1 var0)) (= var3 var4)))))) (inv_main42 var5 var1 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main103 var1 var0 var4) (and (= nullAddr var6) (and (not (= nullAddr var6)) (and (and (and (= var3 var1) (= var5 var0)) (= var2 var4)) (= var6 (inner (getTSLL (read var1 var0))))))))) (inv_main111 var3 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main31 var1 var0 var3 var2)) (inv_main30 (write var1 var3 (O_TSLL (TSLL var2 (inner (getTSLL (read var1 var3)))))) var0 var3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main81 var3 var2 var4 var0 var1) (not (= nullAddr (next (getTSLL (read var3 var1))))))) (inv_main88 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (inv_main69 var2 var1 var3 var0)) (inv_main70 var2 var1 var3 var0 (inner (getTSLL (read var2 var3)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main93 var6 var3 var9 var1 var2) (and (and (and (and (and (= var4 var6) (= var7 var3)) (= var0 var9)) (= var5 var1)) (= var10 var2)) (= var8 (inner (getTSLL (read var6 var2))))))) (inv_main70 var4 var7 var0 var5 var8))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main86 var6 var4 var8 var1 var3) (and (not (= var7 1)) (and (and (and (and (and (= var5 var6) (= var10 var4)) (= var9 var8)) (= var7 var1)) (= var2 var3)) (= var0 (inner (getTSLL (read var6 var3)))))))) (inv_main70 var5 var10 var9 var7 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main96 var5 var2 var10 var0 var1) (and (not (= nullAddr var8)) (and (and (and (and (and (= var7 var5) (= var6 var2)) (= var4 var10)) (= var3 var0)) (= var9 var1)) (= var8 (next (getTSLL (read var5 var10)))))))) (inv_main69 var7 var6 var8 0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Addr) (var6 Heap)) (or (not (and (inv_main26 var4 var3 var5) (and (not (= nullAddr var2)) (and (not (= nullAddr var2)) (and (= var1 0) (and (and (= var6 var4) (= var2 var3)) (= var0 nullAddr))))))) (inv_main69 var6 var2 var2 0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 TSLL) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main32 var3 var1 var6) (and (= var0 0) (and (not (= var5 nullAddr)) (and (not (= nullAddr var5)) (and (and (= var7 (write var3 var6 (O_TSLL (TSLL nullAddr (inner (getTSLL (read var3 var6))))))) (= var2 var1)) (= var5 var6))))))) (inv_main50 (newHeap (alloc var7 (O_TSLL var4))) var2 var5 (newAddr (alloc var7 (O_TSLL var4)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (or (not (and (inv_main76 var3 var2 var4 var0 var1) (not (= nullAddr (inner (getTSLL (read var3 var1))))))) (inv_main83 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr)) (or (not (and (inv_main56 var5 var3 var7 var6) (and (and (= var1 0) (and (= var6 nullAddr) (and (and (and (= var0 var5) (= var2 var3)) (= var4 var7)) (= var10 (inner (getTSLL (read var5 var7))))))) (and (and (and (= var9 var0) (= var8 var2)) (= var11 var4)) (or (and (= var10 nullAddr) (= var1 1)) (and (not (= var10 nullAddr)) (= var1 0))))))) (inv_main54 var9 var8 var11))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (inv_main7 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main11 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main15 var2 var0 var1) (not (is-O_TSLL (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main14 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main14 var1 var0) (not (is-O_TSLL (read var1 (inner (getTSLL (read var1 var0))))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main16 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main16 var1 var0) (not (is-O_TSLL (read var1 (inner (getTSLL (read var1 var0))))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main10 var1 var0) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main21 var2 var1 var0) (and (= var0 nullAddr) (not (is-O_TSLL (read var2 var1))))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (inv_main19 var1 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main31 var1 var0 var3 var2) (not (is-O_TSLL (read var1 var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main30 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main32 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main37 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main42 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main46 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main50 var1 var0 var2 var3) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main49 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main49 var1 var0 var2) (not (is-O_TSLL (read var1 (inner (getTSLL (read var1 var2))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main51 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main51 var1 var0 var2) (not (is-O_TSLL (read var1 (inner (getTSLL (read var1 var2))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main45 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main56 var1 var0 var3 var2) (and (= var2 nullAddr) (not (is-O_TSLL (read var1 var3))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main54 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main64 var1 var0 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr)) (not (and (inv_main69 var2 var1 var3 var0) (not (is-O_TSLL (read var2 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (inv_main78 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main76 var3 var2 var4 var0 var1) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (inv_main83 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main81 var3 var2 var4 var0 var1) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (inv_main88 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main86 var3 var2 var4 var0 var1) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main93 var3 var2 var4 var0 var1) (not (is-O_TSLL (read var3 var1)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (inv_main98 var3 var2 var4 var0 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr)) (not (and (inv_main96 var3 var2 var4 var0 var1) (not (is-O_TSLL (read var3 var4)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main103 var1 var0 var2) (not (is-O_TSLL (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main111 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main109 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main116 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main114 var1 var0 var2) (not (is-O_TSLL (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (inv_main121 var1 var0 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main106 var1 var0 var2) (not (is-O_TSLL (read var1 var0)))))))
(check-sat)
