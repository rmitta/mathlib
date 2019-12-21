--Rohan and Enrico
--Need to import the following from mathlib
import data.set
import data.equiv.tree
namespace prop_logic

--These are propositional formulas
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)
open fml

infixr ` →' `:50 := imp
local notation ` ¬' ` := fml.not

--These are theorems of L
inductive thm : fml → Type
| axk (p q) : thm (p →' q →' p)
| axs (p q r) : thm $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : thm $ (¬'q →' ¬'p) →' p →' q
| mp {p q} : thm p → thm (p →' q) → thm q

lemma p_of_p_of_p_of_p_of_p (p : fml) : thm ((p →' (p →' p)) →' (p →' p)) :=
thm.mp (thm.axk p (p →' p)) (thm.axs p (p →' p) p)

--(1.2.3)
lemma p_of_p (p : fml) : thm (p →' p) :=
thm.mp (thm.axk p p) (p_of_p_of_p_of_p_of_p p)

--These are the consequences of a set of formulas G
--(1.2.4)
inductive consequence (G : set fml) : fml → Type
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ (¬'q →' ¬'p) →' p →' q
| mp {p q} : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g

lemma consequence_of_thm {f : fml} (H : thm f) (G : set fml) : consequence G f :=
begin
  induction H with p q p q r p q p q Hp1 Hpq1 Hp2 Hpq2,
  exact consequence.axk G p q,
  exact consequence.axs G p q r,
  exact consequence.axn G p q,
  exact consequence.mp Hp2 Hpq2,
end

lemma consequence_of_subset {f : fml} {G1 : set fml} {G2 : set fml} (sub : G1 ⊆ G2)
 (H : consequence G1 f) : consequence G2 f :=
begin
  induction H with p q p q r p q p q Hp1 Hpq1 Hp2 Hpq2,
  exact consequence.axk G2 p q,
  exact consequence.axs G2 p q r,
  exact consequence.axn G2 p q,
  exact consequence.mp Hp2 Hpq2,
  exact consequence.of_G _ (sub H_H),
end

lemma thm_of_consequence_empty {f : fml} (H : consequence ∅ f) : thm f :=
begin
  induction H,
  exact thm.axk H_p H_q,
  exact thm.axs H_p H_q H_r,
  exact thm.axn H_p H_q,
  exact thm.mp H_ih_a H_ih_a_1,
  have := set.eq_empty_iff_forall_not_mem.1 (eq.refl ∅) H_g,
  contradiction,
end

--(1.2.5)
theorem deduction (G : set fml) (p q : fml) (H : consequence (G ∪ {p}) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G ((¬' H_q →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp H_ih_a_1 H3,
  exact consequence.mp H_ih_a H4,
  rw set.mem_union at H_H,
  rw classical.or_iff_not_imp_right at H_H,
  have H := @classical.or_not (H_g ∈ {p}),
  apply or.by_cases H,
    intro Hg,
    rw set.mem_singleton_iff at Hg,
    rw Hg,
    exact consequence_of_thm (p_of_p p) G,
  intro Hg,
  have H5 := H_H Hg,
  have H51 := consequence.of_G _ H5,
  have H52 := consequence.axk G H_g p,
  exact consequence.mp H51 H52,
  rw set.mem_singleton_iff,
  apply fml.decidable_eq,
  rw set.mem_singleton_iff,
  apply ne.decidable,
end



--(1.2.6)
lemma hypothetical_syllogism (p q r : fml) (Hpq : thm (p →' q)) (Hqr : thm (q →' r))
 : thm (p →' r) :=
begin
  have H1 := consequence_of_thm Hpq {p},
  have H2 := consequence_of_thm Hqr {p},
  have H3 : consequence {p} p := consequence.of_G p (set.mem_singleton_iff.2 (eq.refl p)),
  have H4 := consequence.mp H3 H1,
  have H5 := consequence.mp H4 H2,
  refine thm_of_consequence_empty (deduction ∅ _ _ _),
  rw [set.union_comm, set.union_empty],
  exact H5,
end

lemma part1 (p : fml) : consequence {¬' (¬' p)} p :=
begin
  have H1 := consequence.axk {¬' (¬' p)} p p,
  have H2 := consequence.axk {¬' (¬' p)} (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p))(set.mem_singleton_iff.2 (eq.refl (¬' (¬' p)))),
  have H4 := consequence.mp H3 H2,
  have H5 := consequence.axn {¬' (¬' p)} (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp H4 H5,
  have H7 := consequence.axn {¬' (¬' p)} (p →' p →' p) p,
  have H8 := consequence.mp H6 H7,
  exact consequence.mp H1 H8,
end

lemma p_of_not_not_p (p : fml) : thm ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction ∅ (¬' (¬' p)) p,
  rw set.empty_union at H1,
  have H2 := H1 (part1 p),
  exact thm_of_consequence_empty H2,
end

lemma not_not_p_of_p (p : fml) : thm (p →' (¬' (¬' p))) :=
begin
  have H1 := thm.axn p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp H2 H1,
end

--(1.2.7)(a)
lemma l127a (p q : fml) : thm ((¬' q) →' (q →' p)) :=
begin
  have H1 := thm.axs (¬' q) ((¬' p) →' (¬' q)) (q →' p),
  have H2 := thm.axn q p,
  have H3 := thm.axk ((¬' p →' ¬' q) →' q →' p) (¬' q),
  have H4 := thm.mp H2 H3,
  have H5 := thm.mp H4 H1,
  have H6 := thm.axk (¬' q) (¬'p),
  have H7 := thm.mp H6 H5,
  exact H7,
end


set_option trace.simplify.rewrite true
---(1.2.7)(b)
lemma l127b (p q : fml) : consequence {(¬' q), q} p :=
begin
  have H1 := l127a p q,
  have H2 := consequence.of_G (¬'q) (_: (¬' q) ∈ {¬' q, q}),
  swap,
  have H21 := set.insert_comm q (¬' q) ∅,
  rw [← set.insert_of_has_insert _ _,
      ← set.insert_of_has_insert _ _,
      ← set.insert_of_has_insert _ _,
      ← set.insert_of_has_insert _ _] at H21,
  apply ((set.ext_iff _ _).1 H21 (¬' q)).2,
  exact set.mem_insert _ _,
  --Why can't I rewrite?

  have H3 := consequence_of_thm H1 {¬' q, q},
  have H4 := consequence.mp H2 H3,
  have H5 := consequence.of_G q (_: q ∈ {¬' q, q}),
  exact consequence.mp H5 H4,
  exact set.mem_insert _ _,

end

--Wow, working with these insert sets is annoying.
lemma l127c1 (p q : fml) : consequence {(¬'p), ((¬'p) →' p)} q :=
begin
  have H0 := l127b q p,
  have H2 :=  set.insert_eq (p) {¬' p},
  unfold insert at H2,
  have H3 := set.union_comm {p} {¬'p},
  rewrite H3 at H2,
  rewrite H2 at H0,
  have H1 : consequence {¬' p} (p →' q),
  exact deduction _ _ _ (H0),

  have H4 : consequence {¬' p, ¬' p →' p} p := consequence.mp
    (consequence.of_G (¬' p) _) (consequence.of_G _ _),
  swap,
  exact set.mem_insert_of_mem _ (set.mem_singleton _),
  swap,
  exact set.mem_insert _ _,

  have H5 : consequence {¬' p, ¬' p →' p} (p →' q) :=
    consequence_of_subset (set.subset_insert _ _) H1,

  exact consequence.mp H4 H5,
end


---(1.2.7)(c)
lemma l127c (p : fml) : thm (((¬' p) →' p) →' p) :=
begin
  have Axiom := thm.axk p p,
  have H1 := l127c1 p (¬'(p →' p →' p)),
  have H1b : {¬' p, ¬' p →' p} = ({¬' p →' p} ∪ {¬' p}) :=
    begin
      rewrite eq.symm (set.insert_eq (¬'p →' p) {¬'p}),
      refl,
    end,
  rewrite H1b at H1,
  have H2 : consequence {¬' p →' p} (¬' p →' (¬' (p →' p →' p))) :=
    deduction _ _ _ H1,

  have H3 := consequence.axn {¬' p →' p} (p →' p →' p) p,
  have H4 := consequence.mp H2 H3,
  have H5 := consequence.mp (consequence_of_thm Axiom _) H4,
  rewrite set.singleton_def (¬' p →' p) at H5,
  rewrite set.insert_eq _ _ at H5,
  rewrite set.union_comm at H5,
  have H6 := deduction _ _ _ H5,
  exact thm_of_consequence_empty H6,

end

--A valuation is an assignment of "truth value" {T, F} to the propositional variables
--i.e. a function (f : fml → {T, F})
--Thus a valuation is a function f : fml → Tval
--We can also define a truth function to be a function f : ((set.range n) → Tval) → Tval
--Or maybe ((ℕ → Tval) → Tval)

--We use bool for our definition of {T, F} because there are theorems proved about it already
--bnot is our not function. We need to define our implies
open bool

def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

--!!
lemma tt_ff_of_bimp_ff {a b : bool} : bimp a b = ff → a = tt ∧ b = ff :=
begin
  rcases a,
  rcases b,
  unfold bimp, simp,
  unfold bimp, simp,
  rcases b,
  unfold bimp, simp, unfold bimp, simp,
end

lemma tt_of_bimp_tt_eq_tt {a : bool} : bimp tt a = tt → a = tt :=
begin
  intro H,
  rcases a,
  exact H,
  exact H,
end

--Sort of concerned about this definition. I almost want to use ℕ → Tval, will I want that
--it is finite and therefore calculatable?
--I might need a definition of what it means for a formula to have variables amognst p1,...pn
--On my second read of it though, it looks fine!
def Tfun : (fml) → (ℕ → bool) → bool
| (atom(i)) v := v i
| (imp a b) v := bimp (Tfun a v) (Tfun b v)
| (not a) v := bnot (Tfun a v)

--f is a tautology if its truth function is always T
def tautology (f : fml) : Prop := ∀ val, Tfun f val = tt

def logically_equivalent (φ ψ : fml) : Prop := Tfun φ = Tfun ψ

--Extended Definition of a valuation (which is a ℕ → Tval) Notice how it is basically Tfun
def prop_val_of_var_val : (ℕ → bool) → fml → bool
| val (atom(i)) := val i
| val (imp a b) := bimp (prop_val_of_var_val val a) (prop_val_of_var_val val b)
| val (not a) := bnot (prop_val_of_var_val val a)

--(1.3.3)
theorem generalisation_of_soundness_of_L {G : set fml} {φ : fml} (H : consequence G φ)
{val : ℕ → bool} (H2 : ∀ p ∈ G, Tfun p val = tt) : Tfun φ val = tt :=
begin
  induction H,
  { by_contradiction h,
    have H1 := eq_ff_of_not_eq_tt h,
    unfold Tfun at H1,
    cases (tt_ff_of_bimp_ff H1) with H2 H3,
    have H4 := tt_ff_of_bimp_ff H3,
    rw H2 at H4,
    cases H4 with H4 H5,
    exact bool.no_confusion H5
    },
  { by_contradiction h,
    have H1 := eq_ff_of_not_eq_tt h,
    unfold Tfun at H1,
    cases (tt_ff_of_bimp_ff H1) with H2 H3,
    cases (tt_ff_of_bimp_ff H3) with H4 H5,
    cases (tt_ff_of_bimp_ff H5) with H6 H7,
    rw H6 at H4,
    have H8 := tt_of_bimp_tt_eq_tt H4,
    rw [H6,H7,H8] at H2,
    exact bool.no_confusion H2,
    },
  { by_contradiction h,
    have H1 := eq_ff_of_not_eq_tt h,
    unfold Tfun at H1,
    cases (tt_ff_of_bimp_ff H1) with H2 H3,
    cases (tt_ff_of_bimp_ff H3) with H4 H5,
    rw [H4, H5] at H2,
    exact bool.no_confusion H2
    },
  { unfold Tfun at H_ih_a_1,
    rw H_ih_a at H_ih_a_1,
    exact tt_of_bimp_tt_eq_tt H_ih_a_1
    },
  exact (H2 _ H_H),
end

--(1.3.1)
theorem soundness_of_L {φ : fml} (H : thm φ) : tautology φ :=
begin
  intro val,
  have H1 := @generalisation_of_soundness_of_L _ _ (consequence_of_thm H ∅) val,
  have H2 : (∀ (p : fml), p ∈ ∅ → Tfun p val = tt),
    intros p Hp, rw set.mem_empty_eq at Hp, contradiction,
  exact H1 H2,
end

--(1.3.6)
--Thinking about the times instead of 'and' - its the same thing! Note that if a type is
-- empty there is an obvious function to false, and otherwise there is no function
def consistent (G : set fml) := ∀ (φ : fml), ((consequence G φ) × (consequence G (¬' φ))) → false

--(1.3.7)
lemma extend_consistent {G : set fml} (H : consistent G) {φ : fml} (H2 : consequence G φ → false) :
 consistent (G ∪ {¬' φ}) :=
begin
  rintros ψ ⟨H3, H4⟩,
  have H5 := deduction _ _ _ H3,
  have H6 := deduction _ _ _ H4,
  have H7 := consequence.mp H6 (consequence.axn _ _ _),
  have H8 := consequence_of_subset (set.subset_union_left G {¬' φ}) H7,
  have H9 := consequence.mp H3 H8,
  have H10 := deduction G _ _ H9,
  have H11 := consequence_of_thm (l127c φ) G,
  have H12 := consequence.mp H10 H11,
  exact H2 H12,
end



--(1.3.8)
lemma lindenbaum {G : set fml} (H : consistent G) : ∃ (G' : set fml),
  ((consistent G') ∧ (∀ (φ : fml), nonempty ((consequence G' φ) ⊕ (consequence G'(¬'φ))))) :=
begin
  sorry,
end


--Attempted defin
lemma minilinden {G : set fml} {φ : fml} : ((consequence G φ) → false) → false :=
begin
--Want this to mean consequence G φ is nonempty
have H : consequence G φ := sorry,
exact λ a, a H,
end
--Conversely want to get an element of consequence G φ from this

lemma minilinden1 {G : set fml} {φ : fml} {H : (consequence G φ → false) → false} :
 nonempty(consequence G φ) :=
begin
  rw imp_false at H,
  have H1 := @not_nonempty_iff_imp_false (consequence G φ),

  have H2 := H1.1,
  have H3 := not.imp H H2,
  have H31 := classical.dec (nonempty (consequence G φ)),
  --DO I have to do this?
  have H4 := (@not_not _ H31).1 H3,
  have H5 := classical.exists_true_of_nonempty H4,
  exact nonempty_of_exists H5,
  --Help

end


--(1.3.4)
theorem completeness_of_L {φ : fml} (H : tautology φ) : thm φ :=
begin
  --Needs conistent defn and lindenbaum lemma
  sorry,
end



end prop_logic

--TODO Truth Functions: (1.1.5)[2], (1.1.7), (1.1.8), (1.1.9)
--TODO:(1.2.7), 1.3.4Onwards
