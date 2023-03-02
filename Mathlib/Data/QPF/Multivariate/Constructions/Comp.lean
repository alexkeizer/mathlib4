/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.comp
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/


universe u

namespace MvQPF

open MvFunctor

variable {n m : ℕ}
  (F : TypeVec.{u} n → Type _)
  (G : Fin2 n → TypeVec.{u} m → Type u)


/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n ↦ G i v
#align mvqpf.comp MvQPF.Comp

namespace Comp

open MvFunctor MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F fun i : Fin2 n ↦ G i α)] : Inhabited (Comp F G α) := I

/-- Constructor for functor composition -/
protected def mk (x : F fun i ↦ G i α) : (Comp F G) α := x
#align mvqpf.comp.mk MvQPF.Comp.mk

/-- Destructor for functor composition -/
protected def get (x : (Comp F G) α) : F fun i ↦ G i α := x
#align mvqpf.comp.get MvQPF.Comp.get

@[simp]
protected theorem mk_get (x : (Comp F G) α) : Comp.mk (Comp.get x) = x := rfl
#align mvqpf.comp.mk_get MvQPF.Comp.mk_get

@[simp]
protected theorem get_mk (x : F fun i ↦ G i α) : Comp.get (Comp.mk x) = x := rfl
#align mvqpf.comp.get_mk MvQPF.Comp.get_mk

section
  variable [MvFunctor F] [∀ i, MvFunctor <| G i]

  /-- map operation defined on a vector of functors -/
  protected def map' : (fun i : Fin2 n ↦ G i α) ⟹ fun i : Fin2 n ↦ G i β := fun _i ↦ map f
  #align mvqpf.comp.map' MvQPF.Comp.map'

  /-- The composition of functors is itself functorial -/
  protected def map : (Comp F G) α → (Comp F G) β :=
    (map fun _i ↦ map f : (F fun i ↦ G i α) → F fun i ↦ G i β)
  #align mvqpf.comp.map MvQPF.Comp.map

  instance : MvFunctor (Comp F G) where map f := Comp.map f

  theorem map_mk (x : F fun i ↦ G i α) :
      f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) ↦ f <$$> x) <$$> x) := rfl
  #align mvqpf.comp.map_mk MvQPF.Comp.map_mk

  theorem get_map (x : Comp F G α) :
      Comp.get (f <$$> x) = (fun i (x : G i α) ↦ f <$$> x) <$$> Comp.get x := rfl
  #align mvqpf.comp.get_map MvQPF.Comp.get_map
end

section
  variable [q : MvQPF F] [q' : ∀ i, MvQPF <| G i]

  instance instMvQPF : MvQPF (Comp F G) where
    P := MvPFunctor.comp (P F) fun i ↦ P <| G i
    abs := Comp.mk ∘ (map fun i ↦ abs) ∘ abs ∘ MvPFunctor.comp.get
    repr {α} := MvPFunctor.comp.mk ∘ repr ∘
                (map fun i ↦ (repr : G i α → (fun i : Fin2 n ↦ Obj (P (G i)) α) i)) ∘ Comp.get
    abs_repr := by intros; simp only [(· ∘ ·), comp.get_mk, abs_repr, map_map,
                                      TypeVec.comp, MvFunctor.id_map', Comp.mk_get]
    abs_map := by intros; simp only [(· ∘ ·)]; rw [← abs_map]
                  simp only [comp.get_map, map_map, TypeVec.comp, abs_map, map_mk]
end

/- section
  variable [p : IsPolynomial F] [p' : ∀ i, IsPolynomial <| G i]

  theorem heq_cast_right {α β β' : Sort _} (a : α) (b : β) {h : β = β'} :
    HEq a (cast h b) = HEq a b :=
  by
    apply propext;
    constructor
    <;> intro premise;
    . have : HEq (cast h b) b := cast_heq _ _
      apply HEq.trans _ this;
      assumption;
    . apply HEq.trans premise;
      apply HEq.symm;
      apply cast_heq;

  theorem heq_cast_left {α α' β : Sort _} (a : α) (b : β) (h : α = α') :
    HEq (cast h a) b = HEq a b :=
  by
    apply propext;
    constructor
    <;> intro premise;
    . have : HEq a (cast h a) := HEq.symm $ cast_heq _ _
      apply HEq.trans this;
      assumption;
    . apply HEq.trans _ premise;
      apply cast_heq;

   theorem hcongr_fun {α : Sort _} {P P' : α → Sort _}
                     {f : (a : α) → P a}
                     {f' : (a : α) → P' a}
                     (a : α)
                     (H₁ : HEq f f')
                     (H₂ : P = P') :
    HEq (f a) (f' a) :=
  by
    cases H₂; cases H₁; rfl;



  theorem hcongr {α α' : Sort _} {P : α → Sort _} {P' : α' → Sort _}
                 {f : (a : α) → P a}
                 {f' : (a' : α') → P' a'}
                 (a : α) (a' : α')
                 (H₁ : HEq f f')
                 (H₂ : HEq a a')
                 (H₃ : α = α')
                 (H₄ : ∀ a, P a = P' (cast H₃ a)) :
    HEq (f a) (f' a') :=
  by
    cases H₂;
    apply hcongr_fun _ H₁;
    funext a;
    simp [cast_eq] at H₃;
    apply H₄;

  theorem cast_arg  {α α' : Sort u₁}
                    {β : α → Sort u₂}
                    {β' : α' → Sort u₂}
                    {f : (a : α) → β a}
                    (a' : α')
                    (h₁ : α' = α)
                    (h₂ : ((a : α) → β a) = ((a' : α') → β' a'))
                    (h₃ : ∀ a', β (cast h₁ a') = β' a') :
    (cast (β:=(a' : α') → β' a') h₂ f) a'
      = cast (h₃ _) (f $ cast h₁ a') :=
  by
    apply eq_of_heq;
    rw [heq_cast_right];
    apply hcongr
    . apply cast_heq
    . apply HEq.symm; apply cast_heq
    . intro a'; apply Eq.symm; apply h₃

  theorem heq_funext {α : Sort u} {β₁ β₂ : α → Sort _}
                      {f₁ : (x : α) → β₁ x}
                      {f₂ : (x : α) → β₂ x}
                      (type_eq : β₁ = β₂ )
                      :
    (∀ (x : α), HEq (f₁ x) (f₂ x)) → HEq f₁ f₂ :=
  by
    intro h;
    apply HEq.trans (b := cast (β:=(x : α) → β₂ x) ?castproof f₁);
    case castproof =>
      cases type_eq; rfl
    case h₁ =>
      apply HEq.symm;
      apply cast_heq
    case h₂ =>
      apply heq_of_eq;
      funext x;
      apply eq_of_heq;
      rw[cast_arg]
      case h₁ => rfl
      case h₃ => intros y; simp only [type_eq, cast_eq]
      simp only [heq_cast_left, cast_eq]
      apply h;


  instance : IsPolynomial (Comp F G) where
    repr_abs := by
      intros α x;
      rcases x with ⟨⟨a', f'⟩, f⟩
      simp only [Comp.get, Comp.mk, Function.comp_apply, repr, abs, ← p.abs_map, p.repr_abs]
      simp [(· <$$> ·), MvPFunctor.map, comp.mk, comp.get, TypeVec.comp]
      congr 2
      {
        funext i b
        rw[(p' i).repr_abs]
      }
      {
        apply heq_funext
        {
          funext i
          congr
          funext j x
          rw[IsPolynomial.repr_abs]
        }
        intro i
        apply heq_funext
        . rfl
        . rfl


      }


      let h : (G · α) ⟹ fun i => Obj (P (G i)) α
        := fun (i : Fin2 n) => @repr _ (G i) _ α
      let x : (P (Comp F G)).Obj α
         := ⟨⟨a', f'⟩, f⟩
      have hh : h = fun (i : Fin2 n) => @repr _ (G i) _ α := rfl;
      have hx : x = ⟨⟨a', f'⟩, f⟩ := rfl;
      rw [←hh, ←hx]
      simp[abs, ←p.abs_map]


      unfold comp.mk
      congr
      .
      have := abs_map (F := F) (α := fun i => G i α) h (p : (P F).Obj _)

      have := abs_map (f:=h) (p)
      conv => {
        arg 1
        arg 1
        arg 1
      }
      simp [←MvQPF.abs_map]
      simp [repr, Comp.get, comp.mk]
      congr
      . conv => {
          arg 1
          arg 1
          arg 1
          rw [←MvQPF.abs_map (f := fun i => repr)]
        }

      aesop
end -/

end Comp

end MvQPF
