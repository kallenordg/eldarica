package lazabs.horn.tests

import ap.api.SimpleAPI
import ap.parser.IExpression._
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses.{Clause, toPrologSyntax}
import lazabs.horn.preprocessor.BooleanClauseSplitter
import ap.parser._
import ap.basetypes.{IdealInt, Leaf, Tree}



object PreprocessorTest extends App{
    lazabs.GlobalParameters.get.assertions = true

    println("Starting preprocessor test...")
    SimpleAPI.withProver(enableAssert = true){ p =>
        import p._
        val c = createConstant("c", Sort.Integer)
        val a = createConstant("a", Sort.Integer)
        val x = createConstant("x", Sort.Integer)
        val y = createConstant("y", Sort.Integer)

        val P1 = createRelation("P1",3)
        val P2 = createRelation("P2",1)

        val clauses = Seq(
            P2(c) :- (P1(a,x,y), (a === 0) ||| (c === x), (a =/= 0) ||| (c === y))
        )
        val firstClause = clauses(0)
        val Clause(headAtom, body, constraint) = firstClause
        val splitter = new BooleanClauseSplitter
        val (newClauses, _, _) = splitter.process(clauses,EmptyVerificationHints)
        val conjuncts =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
        val (atomicConjs, compoundConjs) = conjuncts partition {
        case LeafFormula(_) => true
        case _              => false
      }
        val indexTree =
        Tree(-1, (for (n <- 0 until firstClause.body.size) yield Leaf(n)).toList)
        println("Old clauses")
        clauses.map(_.toPrologString).foreach(println)
        println
        println("New clauses")
        newClauses.map(_.toPrologString).foreach(println)
    }
  
}
