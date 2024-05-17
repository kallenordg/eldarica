/**
 * Copyright (c) 2016-2023 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.preprocessor

import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.Util.{ClauseTermGraph, Dag}
import lazabs.horn.parser.HornReader
import ap.{PresburgerTools, SimpleAPI}
import SimpleAPI.ProverStatus
import ap.basetypes.{IdealInt, Leaf, Tree}
import ap.parser._
import IExpression._
import ap.util.{Seqs, Timeout}
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, HashMap => MHashMap, HashSet => MHashSet}
import scala.languageFeature.reflectiveCalls

object BooleanClauseSplitter {

  private val SPLITTING_TO = 3000
  private val GLOBAL_SPLITTING_TO = 30000

}

/**
 * Elimination of remaining Boolean structure in clauses.
 */
class BooleanClauseSplitter extends HornPreprocessor {
  import HornPreprocessor._
  import BooleanClauseSplitter._

  val name : String = "Boolean clause splitting"

  private var symbolCounter = 0
  private val tempPredicates = new MHashSet[Predicate]
  private val clauseBackMapping = new MHashMap[Clause, (Clause, Tree[Int])]

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {

     val newClauses = SimpleAPI.withProver { p =>
      for (clause <- clauses;
           newClause <- moreCleverSplit(clause)(p)) yield {
        newClause
      }


}

    val translator =
      ClauseShortener.BTranslator.withIndexes(tempPredicates.toSet,
                                              clauseBackMapping.toMap)

    tempPredicates.clear
    clauseBackMapping.clear

    (newClauses, hints, translator)
  }

  private def moreCleverSplit(clause : Clause)
                             (implicit p : SimpleAPI) : Seq[Clause] = {

    if (needsSplittingPos(clause.constraint)) {
      val Clause(headAtom, body, constraint) = clause
      val conjuncts = LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
      val (atomicConjs, compoundConjs) = conjuncts partition {
        case LeafFormula(_) => true
        case _              => false
      }
      if (compoundConjs.size > 3 || getSize(compoundConjs) > 1000){
        clauseGenerator(headAtom,body,constraint)
      }
      else {
        fullDNF(clause)
      }
    } else {
      List(clause)
    }
  }

  private def getSizeSubexpression(subexpression: IExpression): Int = {
    var count = 0
    for (subOfSub <- subexpression.iterator){
      if(subOfSub.length > 1){
        count += getSizeSubexpression(subOfSub)
      }
      else{
        count += 1
      }
    }
    count
  }

  private def getSize(wrappedArray: Seq[IFormula]): Int = {
    var size = 0
    for(iformula <- wrappedArray){
      for(subExpr <- iformula.iterator){
        size = size + getSizeSubexpression(subExpr)
      }
    }
    size
}

private def findOrInstancesPos(f: IFormula): List[IFormula] = f match {
  case IBinFormula(IBinJunctor.Or, _, _) =>
    List(f) 
  case IBinFormula(IBinJunctor.And, f1, f2) =>
    findOrInstancesPos(f1) ++ findOrInstancesPos(f2)
  case INot(f1) =>
    findOrInstancesNeg(f1)
  case _ =>
    List()
}

private def findOrInstancesNeg(f: IFormula): List[IFormula] = f match {
  case IBinFormula(IBinJunctor.And, _, _) =>
    List(f)
  case IBinFormula(IBinJunctor.Or, f1, f2) =>
    findOrInstancesNeg(f1) ++ findOrInstancesNeg(f2)
  case INot(f1) =>
    findOrInstancesPos(f1)
  case _ =>
    List()
}
/** Generates and introduces additional predicates when needed.
  *
  * Given the head, body and constraint of a clause and the clause being an instance of
  * a conjunction containing disjunctions on either right or left hand side of the conjunction.
  * The functions generates predicates for all instances of or-statements. 
  */
private def predicateGenerator(head : IAtom, body: List[IAtom], constraint : IFormula)(implicit p: SimpleAPI): Clauses = {
  var clauses: Clauses = ArrayBuffer.empty[Clause]
  var predicates: List[IAtom] = List.empty[IAtom]
  var constraintWithPredicates = constraint
  if(findOrInstancesPos(constraint) != List()) {
    val listOfDisjunctions = findOrInstancesPos(constraint)
    for(disjunction <- listOfDisjunctions){
      val constants = SymbolCollector constantsSorted disjunction
      val sorts = constants map (Sort sortOf _)
      val pred = MonoSortedPredicate("intPred" + symbolCounter, sorts)
      tempPredicates += pred
      symbolCounter = symbolCounter + 1
      val intLit = IAtom(pred, constants)
      constraintWithPredicates = ExpressionReplacingVisitor(constraintWithPredicates, disjunction, true)
      predicates = predicates ++ List(intLit)
      clauses = clauses ++ clauseGenerator(intLit, List(), disjunction)
    }
    clauses =  clauses ++ Seq(Clause(head, body ++ predicates, constraintWithPredicates))
  }
  clauses

}

/** Generates clauses for handling disjunctions.
  *
  * Given the head, body and constraint of a clause, new clauses in relation
  * to disjuncts and conjuncts are generated being equivalent to the
  * original clause. In case of disjuncts the functions calls itself recursively
  * and if the left or right hand side of a conjunct needs splitting, it's handled
  * by another function.
  */
private def clauseGenerator(head : IAtom, body: List[IAtom], constraint : IFormula)(implicit p: SimpleAPI): Clauses = constraint match{
  case IBinFormula(IBinJunctor.Or, f1, f2) =>
    (needsSplittingPos(f1), needsSplittingPos(f2)) match {
      case (false, false) => Seq(Clause(head, body, f1), Clause(head, body, f2))
      case (true, false) => clauseGenerator(head, body, f1) ++ Seq(Clause(head, body, f2))
      case (false, true) => Seq(Clause(head, body, f1)) ++ clauseGenerator(head, body, f2)
      case (true, true) => clauseGenerator(head, body, f1) ++ clauseGenerator(head, body, f2)
    }
  case IBinFormula(IBinJunctor.And, f1, f2) =>
    (needsSplittingPos(f1), needsSplittingPos(f2)) match {
      case (false, false) => Seq(Clause(head, body, constraint))
      case (true, false) | (false, true)=> predicateGenerator(head, body, constraint)
      case (true, true) => predicateGenerator(head, body, f1) ++ predicateGenerator(head, body, f2) // may need to be the same case as (true,false)|(false,true)
    }
  case _ => Seq.empty
}

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Split disjunctions in a clause body by introducing additional predicates,
   * to avoid combinatorial explosion. The method returns the new clauses,
   * as well as the number of temporary predicates that were needed.
   */
  private def splitWithIntPred(clause : Clause,
                               initialClause : Clause,
                               indexTree : Option[Tree[Int]])
                              (implicit p : SimpleAPI)
                            : (Seq[Clause], Int) = {
    val Clause(headAtom, body, constraint) = clause
    val negConstraint = Transform2NNF(~constraint)

      val conjuncts =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
      val (atomicConjs, compoundConjs) = conjuncts partition {
        case LeafFormula(_) => true
        case _              => false
      }

      if (compoundConjs.size > 3 || getSize(compoundConjs) > 1000) {
        // introduce a new predicate to split the clause into multiple
        // clauses, and this way avoid combinatorial explosion

        // partition the conjuncts
        val leftConsts = new MHashSet[ConstantTerm]
        for (b <- body)
          leftConsts ++= (SymbolCollector constants b)

        val selectedConjs, remainingConjs = new ArrayBuffer[IFormula]
        remainingConjs ++= conjuncts

        var selCompound = 0
        while (selCompound < compoundConjs.size / 2) {
          val sel = remainingConjs minBy { c => {
            val consts = SymbolCollector constants c
            consts.size - (leftConsts & consts).size
          }}

          selectedConjs += sel
          remainingConjs -= sel

          leftConsts ++= SymbolCollector constants sel

          sel match {
            case LeafFormula(_) => // nothing
            case _ => selCompound = selCompound + 1
          }
        }

        val constraint1 = and(selectedConjs)
        val constraint2 = and(remainingConjs)

        val interfaceConstants =
          (SymbolCollector constantsSorted (constraint2 & headAtom)) filter leftConsts

        val intPred =
          MonoSortedPredicate("intPred" + symbolCounter,
                              interfaceConstants map (Sort sortOf _))
        symbolCounter = symbolCounter + 1
        tempPredicates += intPred

        val intLit = IAtom(intPred, interfaceConstants)

        val (newClauses1, preds1) = 
          splitWithIntPred(Clause(intLit, body, constraint1),
                           initialClause, None)
        val (newClauses2, preds2) = 
          splitWithIntPred(Clause(headAtom, List(intLit), constraint2),
                           initialClause,
                           for (it <- indexTree)
                           yield ((0 until (preds1 + 1)) :\ it) {
                                    (n:Int, t:Tree[Int]) => Tree(-1, List(t))
                                  })

        (newClauses1 ++ newClauses2, preds1 + preds2 + 1)

      } else {
        Timeout.withChecker(GlobalParameters.get.timeoutChecker) {
          val newClauses = fullDNF(clause, false)
          for (it <- indexTree) {
            for (newClause <- newClauses)
              clauseBackMapping.put(newClause, (initialClause, it))
          }
          (newClauses, 0)
        }
      }
  }

  private def fullDNF(clause : Clause, addBackMapping : Boolean = true)
                     (implicit p : SimpleAPI) : Seq[Clause] = {
    val Clause(headAtom, body, constraint) = clause

    // transform the clause constraint to DNF, and create a separate
    // clause for each disjunct

    val newClauses =
        if (ContainsSymbol isPresburger constraint) p.scope {
          import p._
          addConstantsRaw(SymbolCollector constantsSorted constraint)
          val disjuncts =
            PresburgerTools.nonDNFEnumDisjuncts(asConjunction(constraint))
          (for (d <- disjuncts; if !d.isFalse)
           yield Clause(headAtom, body, asIFormula(d))).toIndexedSeq
        } else {
          val conjuncts =
            LineariseVisitor(constraint, IBinJunctor.And)
          val (presConjuncts, otherConjuncts) =
            conjuncts partition (ContainsSymbol isPresburger _)

          if (presConjuncts exists (needsSplittingPos _)) p.scope {
            import p._
            val presConstraint  = and(presConjuncts)
            val otherConstraint = and(otherConjuncts)
            addConstantsRaw(SymbolCollector constantsSorted presConstraint)
            val disjuncts =
              PresburgerTools.nonDNFEnumDisjuncts(asConjunction(presConstraint))
            (for (d <- disjuncts; if !d.isFalse)
             yield Clause(headAtom, body,
                          asIFormula(d) & otherConstraint)).toIndexedSeq
          } else {
            List(clause)
          }

// Model-based DNF conversion tends to be too slow here!
//          (for (f <- DNFConverter mbDNF constraint)
//           yield Clause(headAtom, body, f)).toIndexedSeq
        }

    if (addBackMapping) {
      val indexTree =
        Tree(-1, (for (n <- 0 until body.size) yield Leaf(n)).toList)
      for (newClause <- newClauses) 
    clauseBackMapping.put(newClause, (clause, indexTree))
}

    newClauses
  }

  private val globalStartTime = System.currentTimeMillis
  private var clauseGraphCounter = 0

  private def cleverSplit(clause : Clause)
                         (implicit p : SimpleAPI) : Seq[Clause] = {

    if(lazabs.GlobalParameters.get.showClauseGraph) {
      val clauseGraph = new ClauseTermGraph(clause)
      clauseGraph.show(s"clause-graph-$clauseGraphCounter.png")
      clauseGraphCounter += 1
    }

    if (needsSplittingPos(clause.constraint)) {
      // first try the full splitting, but this might sometimes explode
      // val startTime = System.currentTimeMillis
      // def checker() : Unit = {
      //   GlobalParameters.get.timeoutChecker
      //   val currentTime = System.currentTimeMillis
      //   if (currentTime - startTime > SPLITTING_TO ||
      //       currentTime - globalStartTime > GLOBAL_SPLITTING_TO)
      //     Timeout.raise
      // }
      val Clause(headAtom, body, constraint) = clause
      val conjuncts = LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
      val (atomicConjs, compoundConjs) = conjuncts partition {
        case LeafFormula(_) => true
        case _              => false
      }
      if (compoundConjs.size > 3 || getSize(compoundConjs) > 1000){
        val indexTree =
            Tree(-1, (for (n <- 0 until clause.body.size) yield Leaf(n)).toList)
          splitWithIntPred(clause, clause, Some(indexTree))._1
      }
      else {
        fullDNF(clause)
      }
      // val method = 2
      // if (method == 2){
      //   val indexTree =
      //       Tree(-1, (for (n <- 0 until clause.body.size) yield Leaf(n)).toList)
      //     splitWithIntPred(clause, clause, Some(indexTree))._1
      // }
      // else {
      //   fullDNF(clause)
      // }
            
      // Timeout.catchTimeout {
      //   Timeout.withChecker(checker _) { 
      //     fullDNF(clause) }
      // } {
      //   case _ => {
      //     val indexTree =
      //       Tree(-1, (for (n <- 0 until clause.body.size) yield Leaf(n)).toList)
      //     splitWithIntPred(clause, clause, Some(indexTree))._1
      //   }
      // }
    } else {
      List(clause)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def needsSplittingPos(f : IFormula) : Boolean = f match {
    case IBinFormula(IBinJunctor.Or, _, _) =>
      true
    case IBinFormula(IBinJunctor.And, f1, f2) =>
      needsSplittingPos(f1) || needsSplittingPos(f2)
    case INot(f1) =>
      needsSplittingNeg(f1)
    case _ =>
      false
  }

  private def needsSplittingNeg(f : IFormula) : Boolean = f match {
    case IBinFormula(IBinJunctor.And, _, _) =>
      true
    case IBinFormula(IBinJunctor.Or, f1, f2) =>
      needsSplittingNeg(f1) || needsSplittingNeg(f2)
    case INot(f1) =>
      needsSplittingPos(f1)
    case _ =>
      false
  }

}
