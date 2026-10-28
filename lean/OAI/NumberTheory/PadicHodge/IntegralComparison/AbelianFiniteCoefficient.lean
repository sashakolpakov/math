import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.GroupLaw
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.Sections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication

/-! # Abelian Finite Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianFiniteCoefficient

noncomputable section

/-! Actual finite-coefficient H¹ of a smooth proper geometric commutative
group is finite. Multiplication supplies the single finite étale cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction

universe u

theorem finite_of_finite_cover (ℓ n : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} [IsNoetherian X] (U : X.ProEt)
    [IsFinite U.hom] [Surjective U.hom]
    (hzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1,
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 x = 0) :
    Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1) := by
  let e : (⊤_ X.ProEt) ≅ Scheme.ProEt.mk (𝟙 X) :=
    terminalIsTerminal.uniqueUpToIso (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections.Construction.proEtaleIdentityIsTerminal X)
  have hei : IsIso e.hom.left :=
    inferInstanceAs (IsIso (((Scheme.ProEt.forget X) ⋙ Over.forget X).map e.hom))
  have he : e.hom.left = (⊤_ X.ProEt).hom := by
    exact (Category.comp_id e.hom.left).symm.trans (MorphismProperty.Over.w e.hom)
  have : IsIso (⊤_ X.ProEt).hom := he ▸ hei
  let f := terminal.from U
  have hf : f.left = U.hom ≫ inv (⊤_ X.ProEt).hom := by
    apply (cancel_mono (⊤_ X.ProEt).hom).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact MorphismProperty.Over.w f
  have : IsFinite f.left := by rw [hf]; infer_instance
  have : Surjective f.left := by rw [hf]; infer_instance
  have : WeaklyEtale f.left := AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction.proEtaleMorphism_weaklyEtale f
  let D : X.ProEt := Scheme.ProEt.mk (pullback.fst f.left f.left ≫ U.hom)
  have : IsFinite D.hom := inferInstanceAs (IsFinite (pullback.fst f.left f.left ≫ U.hom))
  let d : D.left ⟶ X := D.hom
  have : IsFinite d := inferInstanceAs (IsFinite D.hom)
  have : IsLocallyNoetherian D.left := LocallyOfFiniteType.isLocallyNoetherian d
  have : CompactSpace D.left := QuasiCompact.compactSpace_of_compactSpace d
  have : IsNoetherian D.left := {}
  let a : D ⟶ U := MorphismProperty.Over.homMk (pullback.fst f.left f.left) rfl
  let b : D ⟶ U := MorphismProperty.Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ U.hom = pullback.fst f.left f.left ≫ U.hom
    rw [← MorphismProperty.Over.w f, ← Category.assoc, ← Category.assoc,
      pullback.condition])
  have hD : IsPullback a.left b.left f.left f.left := IsPullback.of_hasPullback f.left f.left
  have := FiniteCoefficient.Sections.sections_finite ℓ n (op D)
  exact IntegralComparison.Finite.CoverFiniteness.finite_of_cover ℓ n U D a b hD hzero

theorem finite (ℓ n : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
    (hℓ : (ℓ : k) ≠ 0) : Finite ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) := by
  have hn : ((ℓ ^ n : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero n hℓ
  have : IsFinite ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A (ℓ ^ n) hn
  have : Etale ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_etale A (ℓ ^ n) hn
  have : Surjective ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A (ℓ ^ n) hn
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := {}
  let U := Scheme.ProEt.mk ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)).left
  have : IsFinite U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A (ℓ ^ n) hn
  have : Surjective U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A (ℓ ^ n) hn
  exact finite_of_finite_cover ℓ n U
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianFiniteCoefficient
