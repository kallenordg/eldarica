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
(declare-datatypes ((HeapObject 0) (cell 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_cell (getcell cell)) (defObj))
                   ((cell (data Int) (next Addr)))))
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
(declare-fun inv_main0 (Heap Addr Int Int Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main16 (Heap Addr Int Int Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main18 (Heap Addr Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main2 (Heap Addr Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main20 (Heap Addr Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Int Int Addr Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main42 (Heap Addr Int Int Addr Addr Addr Addr Addr Int Int) Bool)
(declare-fun inv_main51 (Heap Addr Int Int Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main60 (Heap Addr Int Int Addr Addr Addr Addr Addr Int) Bool)
(declare-fun inv_main64 (Heap Addr Int Int Addr Addr Addr Addr Addr Int Addr) Bool)
(declare-fun inv_main69 (Heap Addr Int Int Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Int Addr Addr Addr Addr Addr Int) Bool)
(assert (forall ((var0 Addr) (var1 Addr)) (inv_main2 emptyHeap var1 1 1 nullAddr nullAddr var0 nullAddr nullAddr)))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int) (var10 Int) (var11 Int)) (or (not (and (inv_main9 var7 var4 var5 var11 var8 var6 var3 var1 var0 var10) (and (= var9 0) (not (= var10 0))))) (inv_main42 var7 var4 var5 var11 var8 var6 var3 var1 var0 var2 var11))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Int) (var3 Addr) (var4 Addr) (var5 Int) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Int) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Heap) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int) (var20 Addr)) (or (not (and (inv_main60 var6 var4 var12 var19 var14 var13 var3 var11 var0 var10) (and (and (and (and (and (and (and (and (and (and (= var15 var6) (= var9 var4)) (= var1 var12)) (= var2 var19)) (= var20 var14)) (= var16 var13)) (= var17 var3)) (= var8 var11)) (= var7 var0)) (= var18 var10)) (= var5 (data (getcell (read var6 var11))))))) (inv_main64 var15 var9 var1 var2 var20 var16 var17 var8 var7 var5 var17))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (= var0 1))) (inv_main2 var8 var5 var6 (+ var0 1) var9 var7 var4 var5 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Int) (var15 Addr) (var16 Addr) (var17 Heap) (var18 Addr) (var19 Int) (var20 Addr)) (or (not (and (inv_main51 var5 var2 var14 var19 var16 var15 var1 var12 var0 var11) (and (and (and (and (and (and (and (and (and (and (= var17 var5) (= var4 var2)) (= var13 var14)) (= var7 var19)) (= var20 var16)) (= var18 var15)) (= var9 var1)) (= var6 var12)) (= var8 var0)) (= var3 var11)) (= var10 (next (getcell (read var5 var12))))))) (inv_main2 var17 var4 var13 var7 var20 var18 var9 var6 var10))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Int) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Heap) (var20 Int)) (or (not (and (inv_main64 var5 var4 var15 var20 var17 var16 var3 var13 var0 var12 var11) (and (and (and (and (and (and (and (and (and (= var19 (write var5 var13 (O_cell (cell (data (getcell (read var5 var13))) var11)))) (= var10 var4)) (= var7 var15)) (= var1 var20)) (= var9 var17)) (= var14 var16)) (= var18 var3)) (= var8 var13)) (= var2 var0)) (= var6 var12)))) (inv_main2 var19 var10 var7 1 var9 var14 var8 var8 var2))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (and (= var3 nullAddr) (= var0 2)))) (inv_main2 var8 var5 var6 1 var9 var7 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (and (not (= var3 nullAddr)) (= var0 2)))) (inv_main2 var8 var5 var6 (+ var0 1) var9 var7 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (and (= var5 var3) (= var0 4)))) (inv_main2 var8 var1 var6 (+ var0 1) var9 var7 var4 var3 var1))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (and (not (= var5 var3)) (= var0 4)))) (inv_main2 var8 var5 var6 1 var9 var7 var4 var3 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Int) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int)) (or (not (and (inv_main20 var6 var5 var12 var17 var14 var13 var4 var10 var0) (and (and (and (and (and (and (and (and (= var16 (write var6 var13 (O_cell (cell (data (getcell (read var6 var13))) nullAddr)))) (= var3 var5)) (= var7 var12)) (= var8 var17)) (= var11 var14)) (= var15 var13)) (= var9 var4)) (= var2 var10)) (= var1 var0)))) (inv_main2 var16 var3 var7 var8 var11 var15 var9 var2 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Int) (var4 Heap) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Heap) (var17 Int)) (or (not (and (inv_main22 var4 var2 var8 var17 var11 var9 var1 var6 var0) (and (and (and (and (and (and (and (and (= var16 (write var4 var9 (O_cell (cell 4 (next (getcell (read var4 var9))))))) (= var13 var2)) (= var3 var8)) (= var10 var17)) (= var12 var11)) (= var5 var9)) (= var14 var1)) (= var15 var6)) (= var7 var0)))) (inv_main2 var16 var13 var3 var10 var12 var5 var14 var15 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (= var8 3))) (inv_main2 var6 var3 (+ var8 1) var9 var3 var5 var2 var1 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Addr)) (or (not (and (inv_main29 var7 var5 var13 var17 var15 var14 var4 var12 var1 var9) (and (and (and (and (and (and (and (and (= var0 (write var7 var14 (O_cell (cell (data (getcell (read var7 var14))) var9)))) (= var8 var5)) (= var11 var13)) (= var2 var17)) (= var10 var15)) (= var18 var14)) (= var6 var4)) (= var3 var12)) (= var16 var1)))) (inv_main2 var0 var8 var11 var2 var10 var18 var6 var3 var16))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (= var8 6))) (inv_main2 var6 var3 1 var9 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (and (= var3 var7) (= var8 5)))) (inv_main2 var6 var5 (+ var8 1) var9 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (and (not (= var3 var7)) (= var8 5)))) (inv_main2 var6 var3 3 var9 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (= var0 3))) (inv_main51 var8 var5 var6 (+ var0 1) var9 var7 var4 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Int) (var14 Addr) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int) (var19 Addr) (var20 Int) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Int) (var29 Addr) (var30 Addr) (var31 Addr) (var32 Addr) (var33 Addr) (var34 Addr) (var35 Addr) (var36 Int) (var37 Heap) (var38 Addr) (var39 Addr) (var40 Addr) (var41 Heap) (var42 Addr) (var43 Addr) (var44 Addr) (var45 Int) (var46 Heap) (var47 Int) (var48 Int) (var49 Addr) (var50 Int) (var51 Addr) (var52 Addr) (var53 Addr) (var54 Int)) (or (not (and (inv_main9 var9 var8 var20 var54 var23 var21 var7 var43 var0 var36) (and (and (and (and (and (and (= var7 nullAddr) (and (and (and (and (and (and (and (and (= var2 var9) (= var53 nullAddr)) (= var17 var20)) (= var47 var54)) (= var27 var23)) (= var22 var21)) (= var42 var7)) (= var15 var43)) (= var49 var0))) (and (and (and (and (and (and (and (and (= var46 var2) (= var30 var53)) (= var48 var17)) (= var26 var47)) (= var33 nullAddr)) (= var29 var22)) (= var32 var42)) (= var24 var15)) (= var25 var49))) (and (and (and (and (and (and (and (and (= var41 var46) (= var44 var30)) (= var13 var48)) (= var6 var26)) (= var31 var33)) (= var14 nullAddr)) (= var4 var32)) (= var16 var24)) (= var19 var25))) (and (and (and (and (and (and (and (and (= var5 var41) (= var35 var44)) (= var50 var13)) (= var18 var6)) (= var3 var31)) (= var38 var14)) (= var39 var4)) (= var34 nullAddr)) (= var51 var19))) (and (and (and (and (and (and (and (and (= var37 var5) (= var12 var35)) (= var45 var50)) (= var28 var18)) (= var52 var3)) (= var11 var38)) (= var40 var39)) (= var1 var34)) (= var10 nullAddr))) (= var36 0)))) (and (or (not (not (= var40 nullAddr))) (inv_main0 var37 var12 var45 var28 var52 var11 var40 var1 var10 1)) (or (not (= var40 nullAddr)) (inv_main0 var37 var12 var45 var28 var52 var11 var40 var1 var10 0))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Int) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Addr) (var16 Int) (var17 Heap) (var18 Addr) (var19 Int) (var20 Int) (var21 Addr) (var22 Int) (var23 Heap) (var24 Int) (var25 Addr) (var26 Addr) (var27 Addr) (var28 Addr) (var29 Addr) (var30 Int) (var31 Addr) (var32 Addr) (var33 Int) (var34 Addr) (var35 Addr) (var36 Addr) (var37 Addr) (var38 Int) (var39 Addr) (var40 Addr) (var41 Addr) (var42 Heap) (var43 Addr) (var44 Addr) (var45 Addr) (var46 Int) (var47 Addr) (var48 Int) (var49 Heap) (var50 Int) (var51 Heap) (var52 Addr) (var53 Addr) (var54 Addr) (var55 Int) (var56 Addr) (var57 Addr) (var58 Addr) (var59 Heap) (var60 Addr) (var61 Addr) (var62 Addr) (var63 Heap) (var64 Addr) (var65 Addr) (var66 Addr) (var67 Addr) (var68 Addr) (var69 Addr) (var70 Addr) (var71 Addr) (var72 Int) (var73 Int)) (or (not (and (inv_main69 var5 var4 var16 var73 var56 var54 var45 var69 var41) (and (and (and (and (and (and (= var58 nullAddr) (and (and (and (and (and (and (and (and (= var59 var51) (= var7 nullAddr)) (= var38 var19)) (= var55 var6)) (= var68 var35)) (= var14 var15)) (= var71 var58)) (= var13 var57)) (= var18 var32))) (and (and (and (and (and (and (and (and (= var42 var59) (= var53 var7)) (= var50 var38)) (= var24 var55)) (= var28 nullAddr)) (= var64 var14)) (= var9 var71)) (= var61 var13)) (= var25 var18))) (and (and (and (and (and (and (and (and (= var63 var42) (= var3 var53)) (= var30 var50)) (= var20 var24)) (= var47 var28)) (= var21 nullAddr)) (= var65 var9)) (= var11 var61)) (= var29 var25))) (and (and (and (and (and (and (and (and (= var49 var63) (= var40 var3)) (= var46 var30)) (= var48 var20)) (= var37 var47)) (= var44 var21)) (= var34 var65)) (= var27 nullAddr)) (= var67 var29))) (and (and (and (and (and (and (and (and (= var23 var49) (= var2 var40)) (= var72 var46)) (= var22 var48)) (= var43 var37)) (= var8 var44)) (= var26 var34)) (= var31 var27)) (= var60 nullAddr))) (and (and (and (and (and (and (and (and (and (and (= var17 var5) (= var12 var4)) (= var0 var16)) (= var33 var73)) (= var10 var56)) (= var62 var54)) (= var36 var45)) (= var1 var69)) (= var70 var41)) (= var52 (next (getcell (read var5 var45))))) (and (and (and (and (and (and (and (and (and (= var51 (write var17 var36 defObj)) (= var39 var12)) (= var19 var0)) (= var6 var33)) (= var35 var10)) (= var15 var62)) (= var66 var36)) (= var57 var1)) (= var32 var70)) (= var58 var52)))))) (and (or (not (not (= var26 nullAddr))) (inv_main0 var23 var2 var72 var22 var43 var8 var26 var31 var60 1)) (or (not (= var26 nullAddr)) (inv_main0 var23 var2 var72 var22 var43 var8 var26 var31 var60 0))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (and (inv_main2 var6 var3 var4 var8 var7 var5 var2 var1 var0) (not (= var3 nullAddr)))) (inv_main9 var6 var3 var4 var8 var7 var5 var2 var1 var0 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Int) (var9 Int) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Int) (var15 Addr) (var16 Addr) (var17 Int) (var18 Int)) (or (not (and (inv_main2 var5 var3 var14 var18 var16 var15 var2 var13 var0) (and (not (= var17 0)) (and (= var3 nullAddr) (and (and (and (and (and (and (and (and (and (= var1 var5) (= var6 var3)) (= var9 var14)) (= var8 var18)) (= var11 var16)) (= var12 var15)) (= var4 var2)) (= var7 var13)) (= var10 var0)) (or (and (not (= 1 var18)) (= var17 1)) (and (= 1 var18) (= var17 0)))))))) (inv_main9 var1 var6 var9 var8 var11 var12 var4 var7 var10 1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Int) (var8 Addr) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Addr) (var18 Int) (var19 Int)) (or (not (and (inv_main2 var5 var3 var15 var19 var17 var16 var2 var14 var0) (and (= var18 0) (and (= var3 nullAddr) (and (and (and (and (and (and (and (and (and (= var1 var5) (= var6 var3)) (= var10 var15)) (= var9 var19)) (= var12 var17)) (= var13 var16)) (= var4 var2)) (= var8 var14)) (= var11 var0)) (or (and (not (= 1 var19)) (= var18 1)) (and (= 1 var19) (= var18 0)))))))) (inv_main9 var1 var6 var10 var9 var12 var13 var4 var8 var11 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int) (var10 Int)) (or (not (and (inv_main9 var6 var3 var4 var10 var7 var5 var2 var1 var0 var8) (and (not (= var9 0)) (not (= var8 0))))) (inv_main16 var6 var3 var4 var10 var7 var5 var2 var1 var0 var4))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 cell) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Heap) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Int) (var12 Int) (var13 Addr) (var14 Addr) (var15 Int) (var16 Addr) (var17 Int) (var18 Addr) (var19 Int) (var20 Addr)) (or (not (and (inv_main16 var7 var5 var12 var19 var14 var13 var4 var9 var1 var15) (and (and (and (and (and (and (and (and (and (and (= var6 (newHeap (alloc var7 (O_cell var3)))) (= var0 var5)) (= var17 (+ var15 1))) (= var11 var19)) (= var2 var14)) (= var20 var13)) (= var10 var4)) (= var8 var9)) (= var18 var1)) (= var16 (newAddr (alloc var7 (O_cell var3))))) (= var15 1)))) (inv_main18 var6 var0 var17 var11 var2 var16 var10 var8 var18))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (= var8 4))) (inv_main29 var6 var3 (+ var8 1) var9 var7 var5 var2 var1 var0 var7))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main9 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (and (not (= var2 nullAddr)) (= var8 0)))) (inv_main69 var6 var3 var4 var9 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Int) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Heap) (var14 Int) (var15 Addr) (var16 Addr) (var17 Addr) (var18 Addr) (var19 Int) (var20 Addr) (var21 Addr) (var22 Addr) (var23 Addr) (var24 Addr) (var25 Addr) (var26 Int) (var27 Addr) (var28 Int)) (or (not (and (inv_main69 var6 var5 var14 var28 var16 var15 var4 var22 var1) (and (not (= var18 nullAddr)) (and (and (and (and (and (and (and (and (and (and (= var13 var6) (= var10 var5)) (= var2 var14)) (= var26 var28)) (= var8 var16)) (= var20 var15)) (= var27 var4)) (= var3 var22)) (= var23 var1)) (= var11 (next (getcell (read var6 var4))))) (and (and (and (and (and (and (and (and (and (= var9 (write var13 var27 defObj)) (= var0 var10)) (= var19 var2)) (= var7 var26)) (= var25 var8)) (= var12 var20)) (= var21 var27)) (= var17 var3)) (= var24 var23)) (= var18 var11)))))) (inv_main69 var9 var0 var19 var7 var25 var12 var18 var17 var24))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (or (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (= var0 5))) (inv_main60 var8 var5 var6 (+ var0 1) var9 var7 var4 var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (or (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (= var8 2))) (inv_main22 var6 var3 (+ var8 1) var9 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (or (not (inv_main18 var6 var3 var4 var8 var7 var5 var2 var1 var0)) (inv_main20 (write var6 var5 (O_cell (cell 0 (next (getcell (read var6 var5)))))) var3 var4 var8 var7 var5 var2 var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (not (and (inv_main18 var6 var3 var4 var8 var7 var5 var2 var1 var0) (not (is-O_cell (read var6 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (not (and (inv_main20 var6 var3 var4 var8 var7 var5 var2 var1 var0) (not (is-O_cell (read var6 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (not (and (inv_main22 var6 var3 var4 var8 var7 var5 var2 var1 var0) (not (is-O_cell (read var6 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Addr) (var9 Int)) (not (and (inv_main29 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (not (is-O_cell (read var6 var5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int) (var9 Int)) (not (and (inv_main16 var6 var3 var4 var9 var7 var5 var2 var1 var0 var8) (and (and (and (and (and (not (= var8 1)) (not (= var8 2))) (not (= var8 3))) (not (= var8 4))) (not (= var8 5))) (not (= var8 6)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int)) (not (and (inv_main51 var7 var4 var5 var9 var8 var6 var3 var2 var0 var1) (not (is-O_cell (read var7 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Int)) (not (and (inv_main60 var7 var4 var5 var9 var8 var6 var3 var2 var0 var1) (not (is-O_cell (read var7 var2)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (not (and (inv_main64 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (not (is-O_cell (read var8 var3)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (not (and (inv_main42 var8 var5 var6 var10 var9 var7 var4 var3 var1 var2 var0) (and (and (and (and (not (= var0 1)) (not (= var0 2))) (not (= var0 3))) (not (= var0 4))) (not (= var0 5)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Addr) (var8 Int)) (not (and (inv_main69 var6 var3 var4 var8 var7 var5 var2 var1 var0) (not (is-O_cell (read var6 var2)))))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Int) (var7 Addr) (var8 Heap) (var9 Addr) (var10 Int)) (not (and (inv_main0 var8 var4 var6 var10 var9 var7 var3 var2 var0 var1) (not (= (read var8 var5) defObj))))))
(check-sat)
