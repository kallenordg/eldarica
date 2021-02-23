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
(declare-datatypes ((HeapObject 0) (TreeNode 0) (StackItem 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_TreeNode (getTreeNode TreeNode)) (O_StackItem (getStackItem StackItem)) (defObj))
                   ((TreeNode (left Addr) (right Addr)))
                   ((StackItem (next Addr) (node Addr)))))
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
(declare-fun inv_main11 (Heap Addr Addr) Bool)
(declare-fun inv_main12 (Heap Addr Addr) Bool)
(declare-fun inv_main14 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr) Bool)
(declare-fun inv_main18 (Heap Addr Addr) Bool)
(declare-fun inv_main22 (Heap Addr Addr) Bool)
(declare-fun inv_main28 (Heap Addr Addr) Bool)
(declare-fun inv_main29 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main30 (Heap Addr Addr) Bool)
(declare-fun inv_main36 (Heap Addr Addr) Bool)
(declare-fun inv_main37 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main38 (Heap Addr Addr) Bool)
(declare-fun inv_main4 (Heap) Bool)
(declare-fun inv_main40 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main41 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main45 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main46 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr) Bool)
(declare-fun inv_main50 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main51 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main54 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main56 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main58 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(declare-fun inv_main62 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main64 (Heap Addr Addr Addr Addr) Bool)
(declare-fun inv_main66 (Heap Addr Addr Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 emptyHeap)) (inv_main4 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Heap) (var3 Int) (var4 TreeNode) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main12 var2 var6 var5) (and (not (= var3 0)) (and (not (= var0 0)) (and (and (and (= var1 var2) (= var8 var6)) (= var7 var5)) (or (and (= (left (getTreeNode (read var2 var5))) nullAddr) (= var0 1)) (and (not (= (left (getTreeNode (read var2 var5))) nullAddr)) (= var0 0)))))))) (inv_main29 (newHeap (alloc var1 (O_TreeNode var4))) var8 var7 (newAddr (alloc var1 (O_TreeNode var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (or (not (and (inv_main14 var0 var2 var1 var3) (= var3 nullAddr))) (inv_main12 var0 var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (inv_main14 var2 var5 var4 var7) (and (= var6 0) (and (not (= var7 nullAddr)) (and (and (and (= var0 var2) (= var1 var5)) (= var3 var4)) (= var6 (right (getTreeNode (read var2 var4))))))))) (inv_main12 var0 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (and (inv_main50 var0 var2 var1 var4 var3) (= (left (getTreeNode (read var0 var1))) nullAddr))) (inv_main51 var0 var2 var1 var4 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main58 var1 var6 var5 var9 var7 var4) (and (and (and (and (= var3 (write var1 var7 (O_StackItem (StackItem (next (getStackItem (read var1 var7))) var4)))) (= var10 var6)) (= var0 var5)) (= var2 var9)) (= var8 var7)))) (inv_main51 var3 var10 var0 var8 var8))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main17 var1 var5 var2) (and (and (and (= var0 var1) (= var4 var5)) (= var3 var2)) (= var6 (left (getTreeNode (read var1 var2))))))) (inv_main11 var0 var4 var6))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr)) (or (not (and (inv_main18 var2 var5 var4) (and (and (and (= var3 var2) (= var6 var5)) (= var0 var4)) (= var1 (right (getTreeNode (read var2 var4))))))) (inv_main11 var3 var6 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (and (inv_main7 var1 var3 var2) (not (= var0 0)))) (inv_main11 var1 var3 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main11 var0 var2 var1)) (inv_main14 var0 var2 var1 (left (getTreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main45 var0 var7 var5 var9 var8) (and (and (and (and (and (= var3 var0) (= var2 var7)) (= var4 var5)) (= var10 var9)) (= var1 var8)) (= var6 (next (getStackItem (read var0 var9))))))) (inv_main46 var3 var2 var4 var6 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 StackItem) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr) (var11 Addr)) (or (not (and (inv_main50 var1 var7 var4 var10 var8) (and (and (and (and (and (and (= var5 (newHeap (alloc var1 (O_StackItem var3)))) (= var11 var7)) (= var2 var4)) (= var6 var10)) (= var9 var8)) (= var0 (newAddr (alloc var1 (O_StackItem var3))))) (not (= (left (getTreeNode (read var1 var4))) nullAddr))))) (inv_main54 var5 var11 var2 var6 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main54 var0 var2 var1 var4 var3)) (inv_main56 (write var0 var3 (O_StackItem (StackItem var4 (node (getStackItem (read var0 var3)))))) var2 var1 var4 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main28 var0 var2 var1)) (inv_main30 (write var0 (left (getTreeNode (read var0 var1))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var0 (left (getTreeNode (read var0 var1))))))))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 StackItem) (var7 Addr) (var8 Addr)) (or (not (and (inv_main7 var2 var8 var4) (and (= var1 0) (and (and (= var0 var2) (= var5 var8)) (= var3 nullAddr))))) (inv_main40 (newHeap (alloc var0 (O_StackItem var6))) var5 var3 (newAddr (alloc var0 (O_StackItem var6))) var7))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main62 var0 var2 var1 var4 var3)) (inv_main64 (write var0 var3 (O_StackItem (StackItem var4 (node (getStackItem (read var0 var3)))))) var2 var1 var4 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main36 var0 var2 var1)) (inv_main38 (write var0 (right (getTreeNode (read var0 var1))) (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var0 (right (getTreeNode (read var0 var1))))))))) var2 var1))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 StackItem) (var10 Addr) (var11 Heap)) (or (not (and (inv_main51 var1 var7 var2 var10 var8) (and (and (and (and (and (and (= var11 (newHeap (alloc var1 (O_StackItem var9)))) (= var6 var7)) (= var3 var2)) (= var5 var10)) (= var4 var8)) (= var0 (newAddr (alloc var1 (O_StackItem var9))))) (not (= (right (getTreeNode (read var1 var2))) nullAddr))))) (inv_main62 var11 var6 var3 var5 var0))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 TreeNode)) (or (not (inv_main4 var0)) (inv_main5 (newHeap (alloc var0 (O_TreeNode var2))) (newAddr (alloc var0 (O_TreeNode var2))) var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main64 var0 var2 var1 var4 var3)) (inv_main66 var0 var2 var1 var4 var3 (right (getTreeNode (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main37 var1 var3 var2 var0)) (inv_main36 (write var1 var2 (O_TreeNode (TreeNode (left (getTreeNode (read var1 var2))) var0))) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main40 var0 var2 var1 var4 var3)) (inv_main41 (write var0 var4 (O_StackItem (StackItem nullAddr (node (getStackItem (read var0 var4)))))) var2 var1 var4 var3))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr)) (or (not (and (inv_main41 var1 var5 var3 var9 var6) (and (not (= var8 nullAddr)) (and (and (and (and (= var0 (write var1 var9 (O_StackItem (StackItem (next (getStackItem (read var1 var9))) var5)))) (= var2 var5)) (= var7 var3)) (= var8 var9)) (= var4 var6))))) (inv_main45 var0 var2 var7 var8 var8))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap) (var8 Addr) (var9 Addr)) (or (not (and (inv_main51 var0 var4 var3 var6 var5) (and (and (not (= var8 nullAddr)) (and (and (and (and (= var7 (write var0 var3 defObj)) (= var2 var4)) (= var9 var3)) (= var8 var6)) (= var1 var5))) (= (right (getTreeNode (read var0 var3))) nullAddr)))) (inv_main45 var7 var2 var9 var8 var8))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Heap) (var10 Addr) (var11 Addr) (var12 Addr) (var13 Addr) (var14 Heap) (var15 Addr)) (or (not (and (inv_main66 var5 var10 var7 var13 var2 var15) (and (and (not (= var1 nullAddr)) (and (and (and (and (= var9 (write var14 var11 defObj)) (= var4 var3)) (= var12 var11)) (= var1 var6)) (= var0 var6))) (and (and (and (and (= var14 (write var5 var2 (O_StackItem (StackItem (next (getStackItem (read var5 var2))) var15)))) (= var3 var10)) (= var11 var7)) (= var8 var13)) (= var6 var2))))) (inv_main45 var9 var4 var12 var1 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (or (not (inv_main29 var0 var3 var2 var1)) (inv_main28 (write var0 var2 (O_TreeNode (TreeNode var1 (right (getTreeNode (read var0 var2)))))) var3 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Int) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main14 var2 var6 var4 var8) (and (not (= var5 0)) (and (not (= var7 0)) (and (not (= var8 nullAddr)) (and (and (and (= var0 var2) (= var1 var6)) (= var3 var4)) (= var7 (right (getTreeNode (read var2 var4)))))))))) (inv_main17 var0 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main30 var0 var2 var1)) (inv_main22 (write var0 (left (getTreeNode (read var0 var1))) (O_TreeNode (TreeNode (left (getTreeNode (read var0 (left (getTreeNode (read var0 var1)))))) nullAddr))) var2 var1))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Heap)) (or (not (and (inv_main12 var1 var3 var2) (and (= var0 0) (and (and (and (= var6 var1) (= var5 var3)) (= var4 var2)) (or (and (= (left (getTreeNode (read var1 var2))) nullAddr) (= var0 1)) (and (not (= (left (getTreeNode (read var1 var2))) nullAddr)) (= var0 0))))))) (inv_main22 var6 var5 var4))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Heap) (var3 Int) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr)) (or (not (and (inv_main12 var2 var5 var4) (and (= var3 0) (and (not (= var0 0)) (and (and (and (= var1 var2) (= var7 var5)) (= var6 var4)) (or (and (= (left (getTreeNode (read var2 var4))) nullAddr) (= var0 1)) (and (not (= (left (getTreeNode (read var2 var4))) nullAddr)) (= var0 0)))))))) (inv_main22 var1 var7 var6))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main5 var0 var2 var1)) (inv_main6 (write var0 var2 (O_TreeNode (TreeNode nullAddr (right (getTreeNode (read var0 var2)))))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main6 var0 var2 var1)) (inv_main7 (write var0 var2 (O_TreeNode (TreeNode (left (getTreeNode (read var0 var2))) nullAddr))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main38 var0 var2 var1)) (inv_main7 (write var0 (right (getTreeNode (read var0 var1))) (O_TreeNode (TreeNode (left (getTreeNode (read var0 (right (getTreeNode (read var0 var1)))))) nullAddr))) var2 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Int) (var6 Addr)) (or (not (and (inv_main22 var0 var4 var1) (and (= var5 0) (and (and (and (= var3 var0) (= var6 var4)) (= var2 var1)) (or (and (= (right (getTreeNode (read var0 var1))) nullAddr) (= var5 1)) (and (not (= (right (getTreeNode (read var0 var1))) nullAddr)) (= var5 0))))))) (inv_main7 var3 var6 var2))))
(assert (forall ((var0 Int) (var1 Int) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Heap)) (or (not (and (inv_main22 var2 var5 var4) (and (= var0 0) (and (not (= var1 0)) (and (and (and (= var7 var2) (= var3 var5)) (= var6 var4)) (or (and (= (right (getTreeNode (read var2 var4))) nullAddr) (= var1 1)) (and (not (= (right (getTreeNode (read var2 var4))) nullAddr)) (= var1 0)))))))) (inv_main7 var7 var3 var6))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Addr) (var9 Addr) (var10 Addr)) (or (not (and (inv_main46 var1 var8 var4 var10 var9) (and (and (and (and (and (= var0 var1) (= var7 var8)) (= var3 var4)) (= var6 var10)) (= var2 var9)) (= var5 (node (getStackItem (read var1 var9))))))) (inv_main50 (write var0 var2 defObj) var7 var5 var6 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Int) (var8 Addr)) (or (not (and (inv_main14 var2 var5 var4 var8) (and (= var7 0) (and (not (= var6 0)) (and (not (= var8 nullAddr)) (and (and (and (= var0 var2) (= var1 var5)) (= var3 var4)) (= var6 (right (getTreeNode (read var2 var4)))))))))) (inv_main18 var0 var1 var3))))
(assert (forall ((var0 TreeNode) (var1 Int) (var2 Int) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Addr) (var7 Addr) (var8 Heap)) (or (not (and (inv_main22 var3 var6 var5) (and (not (= var2 0)) (and (not (= var1 0)) (and (and (and (= var8 var3) (= var4 var6)) (= var7 var5)) (or (and (= (right (getTreeNode (read var3 var5))) nullAddr) (= var1 1)) (and (not (= (right (getTreeNode (read var3 var5))) nullAddr)) (= var1 0)))))))) (inv_main37 (newHeap (alloc var8 (O_TreeNode var0))) var4 var7 (newAddr (alloc var8 (O_TreeNode var0)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (or (not (inv_main56 var0 var2 var1 var4 var3)) (inv_main58 var0 var2 var1 var4 var3 (left (getTreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main5 var0 var2 var1) (not (is-O_TreeNode (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main6 var0 var2 var1) (not (is-O_TreeNode (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main11 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (not (and (inv_main14 var0 var2 var1 var3) (and (not (= var3 nullAddr)) (not (is-O_TreeNode (read var0 var1))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main17 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main18 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main12 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr)) (not (and (inv_main29 var0 var3 var2 var1) (not (is-O_TreeNode (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main28 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main28 var0 var2 var1) (not (is-O_TreeNode (read var0 (left (getTreeNode (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main30 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main30 var0 var2 var1) (not (is-O_TreeNode (read var0 (left (getTreeNode (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main22 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main37 var1 var3 var2 var0) (not (is-O_TreeNode (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main36 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main36 var0 var2 var1) (not (is-O_TreeNode (read var0 (right (getTreeNode (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main38 var0 var2 var1) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main38 var0 var2 var1) (not (is-O_TreeNode (read var0 (right (getTreeNode (read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main40 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main41 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main45 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main46 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main50 var0 var2 var1 var4 var3) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main54 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main56 var0 var2 var1 var4 var3) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main58 var0 var3 var2 var5 var4 var1) (not (is-O_StackItem (read var0 var4)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main51 var0 var2 var1 var4 var3) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main62 var0 var2 var1 var4 var3) (not (is-O_StackItem (read var0 var3)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr)) (not (and (inv_main64 var0 var2 var1 var4 var3) (not (is-O_TreeNode (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr) (var3 Addr) (var4 Addr) (var5 Addr)) (not (and (inv_main66 var0 var2 var1 var4 var3 var5) (not (is-O_StackItem (read var0 var3)))))))
(check-sat)
