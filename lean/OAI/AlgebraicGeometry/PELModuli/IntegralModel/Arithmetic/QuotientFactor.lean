import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyFactorizationIs
import OAI.ArithmeticGeometry.Models.FoundationsPullback
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Quotient Factor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientFactor

noncomputable section

/-! A factor of an arithmetic fpqc group quotient descends from a
faithfully flat scalar extension when the composite is already arithmetic.
The factor and its exact scalar-extension equality are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem property_of_fpqc_baseChange {S S' : Scheme}
    (u : S' ⟶ S) [Flat u] [Surjective u] [QuasiCompact u]
    (P : MorphismProperty Scheme)
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {A B : Over S} (f : A ⟶ B) (hf : P ((Over.pullback u).map f).left) : P f.left :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback u f)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hf

variable {S S' : Scheme} (u : S' ⟶ S) [Flat u] [Surjective u] [QuasiCompact u]
  {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (q : A ⟶ B) (p : A ⟶ C) [IsMonHom q] [IsMonHom p]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

/-- The arithmetic quotient and composite uniquely determine the
descended group homomorphism and recover the specified scalar-extended map. -/
theorem quotient_factor_descends
    (h : (Over.pullback u).obj B ⟶ (Over.pullback u).obj C) [IsMonHom h]
    (hh : (Over.pullback u).map q ≫ h = (Over.pullback u).map p) :
    ∃! r : B ⟶ C, IsMonHom r ∧ q ≫ r = p ∧ (Over.pullback u).map r = h := by
  let F := Over.pullback u
  have hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ q = 1 → x ≫ p = 1 := by
    intro T x hx
    apply F.map_injective
    rw [F.map_comp, F.map_one, ← hh, ← Category.assoc]
    have hqx : F.map x ≫ F.map q = 1 :=
      (F.map_comp x q).symm.trans ((congrArg F.map hx).trans F.map_one)
    rw [hqx, MonObj.one_comp]
  obtain ⟨r, ⟨hr, hqr⟩, hu⟩ := IsogenyFactorizationIs.IsogenyFactorization.fpqc_group_hom_descent q p hk
  have : Flat (F.map q).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback u q).flip inferInstance
  have : Surjective (F.map q).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback u q).flip inferInstance
  have : QuasiCompact (F.map q).left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback u q).flip inferInstance
  have : EffectiveEpi (F.map q) := IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc (F.map q)
  have he : F.map r = h := by
    apply (cancel_epi (F.map q)).mp
    exact (F.map_comp q r).symm.trans ((congrArg F.map hqr).trans hh.symm)
  exact ⟨r, ⟨hr, hqr, he⟩, fun a ha => hu a ⟨ha.1, ha.2.1⟩⟩

variable {T : Scheme} {X Y Z W : Over T} [GrpObj X] [GrpObj Y]

theorem group_iso_conjugate_power (e : X ≅ Y) [IsMonHom e.hom] (n : ℕ) :
    e.hom ≫ ((𝟙 Y : Y ⟶ Y) ^ n) ≫ e.inv = (𝟙 X : X ⟶ X) ^ n := by
  rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, e.hom_inv_id]

omit [GrpObj X] in
theorem reverse_factor_of_power_composite
    (e : X ≅ Y) (q : X ⟶ Z) (v : Z ≅ W) (d : Y ⟶ W) (f : W ⟶ Y)
    (hd : e.inv ≫ q ≫ v.hom = d) (n : ℕ) (hf : d ≫ f = (𝟙 Y : Y ⟶ Y) ^ n) :
    q ≫ (v.hom ≫ f ≫ e.inv) = e.hom ≫ ((𝟙 Y : Y ⟶ Y) ^ n) ≫ e.inv := by
  apply (cancel_epi e.inv).mp
  calc
    _ = (e.inv ≫ q ≫ v.hom) ≫ f ≫ e.inv := by simp only [Category.assoc]
    _ = d ≫ f ≫ e.inv := by rw [hd]
    _ = ((𝟙 Y : Y ⟶ Y) ^ n) ≫ e.inv := by rw [← Category.assoc, hf]
    _ = _ := by simp only [e.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.QuotientFactor
