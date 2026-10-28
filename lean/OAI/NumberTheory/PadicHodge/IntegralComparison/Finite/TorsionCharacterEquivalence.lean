import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCocycleEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleSurjectivity

/-! # Torsion Character Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TorsionCharacterEquivalence

noncomputable section

/-! Actual finite-coefficient H¹ of an abelian variety is the additive
dual of its actual finite torsion-point group. Both directions come from
the multiplication-cover cocycle and the native sheaf Ext construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "m" => ((𝟙 A : A ⟶ A) ^ (ℓ ^ n))

theorem exists_overlap_class (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) →+ ZMod (ℓ ^ n)) :
    ∃ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1,
      MultiplicationCoverCharacter.character ℓ n A hℓ x =
        MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ := by
  let U := MultiplicationCoverCharacter.cover ℓ n A hℓ
  let D := MultiplicationCoverCharacter.overlap ℓ n A hℓ
  let a := MultiplicationCoverCharacter.first ℓ n A hℓ
  let b := MultiplicationCoverCharacter.second ℓ n A hℓ
  let e : (⊤_ A.left.ProEt) ≅ Scheme.ProEt.mk (𝟙 A.left) :=
    terminalIsTerminal.uniqueUpToIso (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections.Construction.proEtaleIdentityIsTerminal A.left)
  let e' := ((Scheme.ProEt.forget A.left) ⋙ Over.forget A.left).mapIso e
  have he : e'.hom = (⊤_ A.left.ProEt).hom :=
    (Category.comp_id e.hom.left).symm.trans (MorphismProperty.Over.w e.hom)
  let : IsIso (⊤_ A.left.ProEt).hom := he ▸ inferInstanceAs (IsIso e'.hom)
  let f := terminal.from U
  have hf : f.left = U.hom ≫ inv (⊤_ A.left.ProEt).hom := by
    apply (cancel_mono (⊤_ A.left.ProEt).hom).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact MorphismProperty.Over.w f
  have hn : ((ℓ ^ n : ℕ) : k) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ
  let : IsFinite U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A (ℓ ^ n) hn
  let : Surjective U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A (ℓ ^ n) hn
  let : IsFinite f.left := by rw [hf]; infer_instance
  let : Surjective f.left := by rw [hf]; infer_instance
  have hD : IsPullback a.left b.left f.left f.left := by
    change IsPullback (pullback.fst (m).left (m).left) (pullback.snd (m).left (m).left) f.left f.left
    refine (IsPullback.of_hasPullback (m).left (m).left).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e'
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) ?_ ?_
    · change 𝟙 A.left ≫ (m).left = f.left ≫ e'.hom
      rw [Category.id_comp, he]
      exact (MorphismProperty.Over.w f).symm
    · change 𝟙 A.left ≫ (m).left = f.left ≫ e'.hom
      rw [Category.id_comp, he]
      exact (MorphismProperty.Over.w f).symm
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let : PreconnectedSpace U.left := inferInstanceAs (PreconnectedSpace A.left)
  let S := CoverCharacter.presentation ℓ n A.left
  let hS := CoverCharacter.presentation_shortExact ℓ n (X := A.left)
  let hlift := CoverFiniteness.presentation_local_lifts ℓ n S.X₂ S.X₃ S.f S.g S.zero hS U
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
  obtain ⟨x, hx⟩ := CoverCocycleSurjectivity.exists_class U D a b hD S hS hlift
    (CoverCharacter.coefficient_restrictions_eq ℓ n a b)
    (MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ)
    (MultiplicationOverlapCocycles.cocycle_condition ℓ n A hℓ χ)
  change MultiplicationCoverCharacter.character ℓ n A hℓ x =
    MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ at hx
  exact ⟨x, hx⟩

theorem character_eq_of_overlap_eq
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) →+ ZMod (ℓ ^ n))
    (hx : MultiplicationCoverCharacter.character ℓ n A hℓ x =
      MultiplicationOverlapCocycles.cocycle ℓ n A hℓ χ) :
    TorsionPointCharacter.character ℓ n A hℓ x = χ := by
  let D := MultiplicationCoverCharacter.overlap ℓ n A hℓ
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  apply AddMonoidHom.ext
  intro t
  let p := TorsionPointCharacter.pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t.toMul
  let z : A.left := Classical.choice inferInstance
  have hv := congrArg (fun s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op D) =>
    ULift.down (α := C(A.left, ZMod (ℓ ^ n)))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map p.op s) z) hx
  rw [TorsionPointCharacter.pair_value,
    MultiplicationCocycleEvaluation.cocycle_pair_value] at hv
  exact hv

theorem character_surjective : Function.Surjective (TorsionPointCharacter.character ℓ n A hℓ) := by
  intro χ
  obtain ⟨x, hx⟩ := exists_overlap_class ℓ n A hℓ χ
  exact ⟨x, character_eq_of_overlap_eq ℓ n A hℓ x χ hx⟩

theorem character_cocycle_formula (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    MultiplicationCoverCharacter.character ℓ n A hℓ x =
      MultiplicationOverlapCocycles.cocycle ℓ n A hℓ
        (TorsionPointCharacter.character ℓ n A hℓ x) := by
  obtain ⟨y, hy⟩ := exists_overlap_class ℓ n A hℓ
    (TorsionPointCharacter.character ℓ n A hℓ x)
  have he : y = x := TorsionPointCharacter.character_injective ℓ n A hℓ
    (character_eq_of_overlap_eq ℓ n A hℓ y _ hy)
  exact he ▸ hy

def equiv : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 ≃+
    (Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) →+ ZMod (ℓ ^ n)) :=
  AddEquiv.ofBijective (TorsionPointCharacter.character ℓ n A hℓ)
    ⟨TorsionPointCharacter.character_injective ℓ n A hℓ,
      character_surjective ℓ n A hℓ⟩

@[simp] theorem equiv_apply (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    equiv ℓ n A hℓ x = TorsionPointCharacter.character ℓ n A hℓ x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TorsionCharacterEquivalence
