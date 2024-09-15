package lazabs.horn.tests

import ap.api.SimpleAPI
import ap.parser.IExpression._
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses.{Clause, toPrologSyntax}
import lazabs.horn.preprocessor.BooleanClauseSplitter
import ap.parser._
import ap.basetypes.{IdealInt, Leaf, Tree}

object SplittingExample extends App{
    lazabs.GlobalParameters.get.assertions = true

    println("Starting preprocessor test...")
    SimpleAPI.withProver(enableAssert = true){ implicit p =>
        import p._
        val c = createConstant("c", Sort.Integer)
        val a = createConstant("a", Sort.Integer)
        val b = createConstant("b", Sort.Integer)

        val Q = createRelation("Q",1)
        val P = createRelation("P",3)

        val clauses = Seq(
            Q(a+1) :- (P(a,b,c),((a >= b &&& a === c) ||| ((a < b ||| b == c) ||| ((a === b)&&&(b===c|||a===c)))))
        )
        val firstClause = clauses(0)
        val Clause(headAtom, body, constraint) = firstClause
        val splitter = new BooleanClauseSplitter
        val indexTree =
        Tree(-1, (for (n <- 0 until firstClause.body.size) yield Leaf(n)).toList)
        val (newClauses) = splitter.clauseGenerator(firstClause,firstClause,Some(indexTree))
        println("Old clauses")
        clauses.map(_.toPrologString).foreach(println)
        println
        println("New clauses")
        newClauses.map(_.toPrologString).foreach(println)
        newClauses.foreach { clause =>
            assert(clause.body.size <= 1, "Each clause should have a body size of 1")
}
    }
  
}
