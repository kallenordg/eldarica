package lazabs.horn.tests

import ap.api.SimpleAPI
import ap.parser.IExpression._
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses.{Clause, toPrologSyntax}
import lazabs.horn.preprocessor.BooleanClauseSplitter
import ap.parser._
import ap.basetypes.{IdealInt, Leaf, Tree}



object NonLinearTest extends App{
    lazabs.GlobalParameters.get.assertions = true

    println("Starting non-linear test...")
    SimpleAPI.withProver(enableAssert = true){ implicit p =>
        import p._
        val a = createConstant("a", Sort.Integer)
        val b = createConstant("b", Sort.Integer)
        val c = createConstant("c", Sort.Integer)
        val d = createConstant("d", Sort.Integer)
        val e = createConstant("e", Sort.Integer)

        val P = createRelation("P",4)
        val Q = createRelation("Q",4)

        val clauses = Seq(
            Q(a,b,c,d) :- (P(a,b,c,d), ((a =/= 0 ||| b === 0 ) &&& (e === 0 ||| c === 0) ||| d === 0))
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
