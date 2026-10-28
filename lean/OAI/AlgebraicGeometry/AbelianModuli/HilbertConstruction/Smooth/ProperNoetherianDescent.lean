import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.NoetherianSchemeDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatedFiniteCoefficientDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteCoefficientDescent

/-! # Proper Noetherian Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperNoetherianDescent

noncomputable section

/-! Smooth proper schemes over arbitrary rings have smooth proper
Noetherian models with Cartesian recovery of the original scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem proper_baseChange_of_cartesian
    {S T : Scheme} (X : Over S) (Y : Over T)
    [IsProper X.hom] (b : S ⟶ T) (q : X.left ⟶ Y.left)
    (H : IsPullback q X.hom Y.hom b) :
    IsProper ((Over.pullback b).obj Y).hom := by
  have h : IsProper (H.isoPullback.inv ≫ X.hom) := inferInstance
  change IsProper (pullback.snd Y.hom b)
  exact H.isoPullback_inv_snd ▸ h

private theorem exists_finiteCoefficient_cartesian_lift
    (C R : Type) [CommRing C] [CommRing R] [Algebra C R]
    (X : Over (Spec (.of R))) (Y : Over (Spec (.of C))) (q : X.left ⟶ Y.left)
    (H : IsPullback q X.hom Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap C R)))) (s : Finset R) :
    ∃ q' : X.left ⟶ ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C R s)).obj Y).left,
      IsPullback q' X.hom ((Over.pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C R s)).obj Y).hom
        (ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange.Abelian.objectCoefficientPoint C R s) := by
  let b := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C R s
  let p := ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange.Abelian.objectCoefficientPoint C R s
  have hp : p ≫ b = Spec.map (CommRingCat.ofHom (algebraMap C R)) := by
    dsimp only [p, b, ArithmeticGeometry.Descent.CMVariety.CoefficientObjectBaseChange.Abelian.objectCoefficientPoint, ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap]
    rw [← Spec.map_comp]
    congr 1
  have H' : IsPullback q X.hom Y.hom (p ≫ b) := by
    rw [hp]
    exact H
  exact ⟨_, H'.of_right' (IsPullback.of_hasPullback Y.hom b)⟩

theorem exists_smooth_proper_noetherian_scheme_model
    {R : Type} [CommRing R] (X : Over (Spec (.of R)))
    [Smooth X.hom] [IsProper X.hom] :
    ∃ C : Subalgebra ℤ R, Algebra.FiniteType ℤ C ∧ IsNoetherianRing C ∧
      ∃ Y : Over (Spec (.of C)), Smooth Y.hom ∧ IsProper Y.hom ∧
        ∃ q : X.left ⟶ Y.left, IsPullback q X.hom Y.hom
          (Spec.map (CommRingCat.ofHom C.val.toRingHom)) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ R) :=
    (Subalgebra.fg_iff_finiteType _).mp Subalgebra.fg_bot
  obtain ⟨C, _, hC, hCN, Y, hYS, hYN, q, H⟩ :=
    NoetherianSchemeDescent.exists_smooth_noetherian_scheme_model_above X ⊥
  have : Algebra.FiniteType ℤ C := hC
  have : IsNoetherianRing C := hCN
  have : Smooth Y.hom := hYS
  have : IsNoetherian Y.left := hYN
  have H₀ : IsPullback q X.hom Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap C R))) := H
  have : IsProper ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap C R)))).obj Y).hom :=
    proper_baseChange_of_cartesian X Y _ q H₀
  obtain ⟨s, hsep⟩ := SeparatedFiniteCoefficientDescent.separated_eventually_of_finiteType C R Y
  let D : Subalgebra C R := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra C R s
  let bD := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap C R s
  let YD : Over (Spec (.of D)) := (Over.pullback bD).obj Y
  have hD : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.trans (S := C) hC (inferInstanceAs (Algebra.FiniteType C D))
  have : Algebra.FiniteType ℤ D := hD
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℤ D
  have : Smooth YD.hom := inferInstanceAs (Smooth (pullback.snd Y.hom bD))
  have : IsSeparated YD.hom := hsep
  have : QuasiCompact YD.hom := inferInstanceAs (QuasiCompact (pullback.snd Y.hom bD))
  have : IsNoetherian YD.left := Finite.TypeParameterNoetherian.finiteType_noetherian_source YD.hom
  obtain ⟨qD, HD⟩ := exists_finiteCoefficient_cartesian_lift C R X Y q H₀ s
  have HD₀ : IsPullback qD X.hom YD.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D R))) := HD
  have : IsProper ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D R)))).obj YD).hom :=
    proper_baseChange_of_cartesian X YD _ qD HD₀
  obtain ⟨t, hproper⟩ := Proper.FiniteCoefficientDescent.proper_eventually_of_separated_noetherian_model D R YD
  let E : Subalgebra D R := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra D R t
  let bE := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap D R t
  let YE : Over (Spec (.of E)) := (Over.pullback bE).obj YD
  have hE : Algebra.FiniteType ℤ E :=
    Algebra.FiniteType.trans (S := D) hD (inferInstanceAs (Algebra.FiniteType D E))
  have : Algebra.FiniteType ℤ E := hE
  have hEN : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing ℤ E
  have hYES : Smooth YE.hom := inferInstanceAs (Smooth (pullback.snd YD.hom bE))
  have hYEP : IsProper YE.hom := hproper
  obtain ⟨qE, HE⟩ := exists_finiteCoefficient_cartesian_lift D R X YD qD HD₀ t
  exact ⟨E.restrictScalars ℤ, hE, hEN, YE, hYES, hYEP, qE, HE⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProperNoetherianDescent
