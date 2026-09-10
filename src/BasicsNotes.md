# Basics

[Book chapter](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html)

[Software Foundations in Coq](https://www.youtube.com/watch?list=PLre5AT9JnKShFK9l9HYzkZugkJSsXioFs) (videos from 1 to 20)

[Code](Basics.v)

## What I learned

The first chapter of the book from its name it's about basics. The chapter was mainly about introducing the syntax, different proof tactics and how to use them.

I didn't have any problem with the syntax because the language is similar to ML-syntax which I'm familiar with.

The real problem that I had during the whole chapter is reduction tactics. For example, `reflexivity` seemed like something magical. It reduces the expressions and check for equality and during the whole chapter I was curious how it works. But the chapter didn't talk about it at all.

Another thing that really amused me was solving the `andb_true_elim2` exercise. In one of the cases, I ended up with a contradiction in the hypothesis that states `false = true` while my goal was also `false = true`, and initially thought that the theorem is unprovable. Then I saw that one of the hints in the book was essentially to rewrite using the contradiction.

I still don't understand how can you end up with a hypothesis like this and then use it to turn a `false = true` to `true = true` to finish your proof with reflexivity. But I assume it's because it's a hypothesis and not a proof itself. Technically, no one proved that `false = true`, we just used it as an assumption.

I was also watching **Software Foundations in Coq** by Michael Clarkson and I was lucky that one of the videos was about reduction tactics. In that videos, he explained that Coq actually consists of 3 different languages:

- Vernacular

  These are the top-level commands. Examples: `Check`, `Theorem`, `Proof`, `Qed`.

- Gallina
  
  This is the functional programming language in Rocq. Examples: `match`, `if`, `forall`.

- Ltac

  These are the tactics used in the proofs. Examples: `intros`, `simpl`, `reflexivity`, `destruct`.

In the tactics languages, we have `reflexivity` and `simpl`. From what I understand these two techniques try to reduce the expressions passed to them. `simpl` attempts to do smart choices on how to reduce the expression to make it easy for humans to look at a simplified expression. It tries to do full reduction, however it won't attempt to expand names unless doing so causes a pattern match to simplify the expression.

On the other hand, reflexivity does do full reduction of the expression then it checks if the left and right expressions are alpha equivalent, if true the goal is solved, otherwise it fails.
