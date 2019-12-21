--Need to import the following from mathlib
import data.set
import data.equiv.tree
--This is Ed's encodable trees file
namespace prop_logic

@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)
--Want to show that the set of fml is countable. First step: build tree ℕ and show
-- that fml injects into it

definition f : fml → tree ℕ
| (fml.atom i) := tree.node (i+2) tree.nil tree.nil
| (fml.imp a b) := tree.node 0 (f a) (f b)
| (fml.not a) := tree.node 1 tree.nil (f a)

def option_map_imp : option fml → option fml → option fml
| option.none (option.some p) := option.none
| (option.some p) option.none := option.none
| option.none option.none := option.none
| (option.some p) (option.some q) := option.some (fml.imp p q)

definition finv : tree ℕ → option fml
| tree.nil := option.none
| (tree.node (i+2) tree.nil tree.nil) := option.some (fml.atom i)
| (tree.node (i+2) tree.nil (tree.node _ _ _)) := option.none
| (tree.node (i+2) (tree.node _ _ _) _) := option.none
| (tree.node 0 a b) := ((option_map_imp) (finv a) (finv b))
| (tree.node 1 tree.nil a) := (option.map fml.not) (finv a)
| (tree.node 1 (tree.node _ _ _) _) := option.none


lemma encodable_fml : encodable fml :=
begin
    apply encodable.of_left_injection (f : fml → tree ℕ) (finv) _,
    intro p,
    induction p,
            refl,
        unfold f, unfold finv,
        rewrite p_ih_a, rewrite p_ih_b, refl,
    unfold f, unfold finv, rewrite p_ih, refl,
end

lemma denumerable_fml : denumerable fml :=
begin
    apply denumerable.of_encodable_of_infinite _,
        exact encodable_fml,
    exact infinite.of_injective (λ (i : ℕ), fml.atom i) (λ a b H, (fml.atom.inj H)),
end

--now use denumerable.of_nat as your bijection to "list the propositions p1,p2,p3,..."

--Next step: Create lindenbaum style extension of a set of formulas
end prop_logic
