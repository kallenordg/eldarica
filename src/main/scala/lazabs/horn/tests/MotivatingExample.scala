package lazabs.horn.tests

import ap.api.SimpleAPI
import ap.parser.IExpression._
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses.{Clause, toPrologSyntax}
import lazabs.horn.preprocessor.BooleanClauseSplitter
import ap.parser._
import ap.basetypes.{IdealInt, Leaf, Tree}

object MotivatingExample extends App{
    lazabs.GlobalParameters.get.assertions = true

    println("Starting preprocessor test...")
    SimpleAPI.withProver(enableAssert = true){ implicit p =>
        import p._
        val c = createConstant("c", Sort.Integer)
        val a = createConstant("a", Sort.Integer)
        val b = createConstant("b", Sort.Integer)
        val d = createConstant("d", Sort.Integer)
        val e = createConstant("e", Sort.Integer)
        val f = createConstant("f", Sort.Integer)
        val t = createConstant("t", Sort.Integer)
        val u = createConstant("u", Sort.Integer)
        val v = createConstant("v", Sort.Integer)
        val w = createConstant("w", Sort.Integer)
        val x = createConstant("x", Sort.Integer)
        val y = createConstant("y", Sort.Integer)

        val P1 = createRelation("P1",9)
        val P2 = createRelation("P2",3)

        val clauses = Seq(
            P2(c,d,f) :- (P1(a,x,y,b,v,w,e,t,u), (((((a === 0) &&& (c === x)) |||((a =/= 0) &&& (c === y)))) &&& ((((b === 0) &&& (d === v)) |||((b =/= 0) &&& (d === w))))&&& ((((e === 0) &&& (f === t)) |||((e =/= 0) &&& (f === u))))))
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
