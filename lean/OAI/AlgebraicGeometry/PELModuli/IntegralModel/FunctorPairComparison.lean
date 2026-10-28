import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection

/-! # Functor Pair Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairComparison

noncomputable section

/-! Product comparisons induced by the two given family isomorphisms,
with their projections retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {T : Scheme.{w}} (F : C ⥤ Over T) [F.Monoidal] (D A : C)
    {D' A' : Over T} (eD : F.obj D ≅ D') (eA : F.obj A ≅ A')

def functorPairComparison : F.obj (D ⊗ A) ≅ D' ⊗ A' :=
  (Functor.Monoidal.μIso F D A).symm ≪≫ tensorIso eD eA

theorem functorPairComparison_fst :
    (functorPairComparison F D A eD eA).hom ≫ fst D' A' = F.map (fst D A) ≫ eD.hom := by
  simp only [functorPairComparison, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso_hom]
  rw [Category.assoc, tensorHom_fst, ← Category.assoc, Functor.OplaxMonoidal.δ_fst]

theorem functorPairComparison_snd :
    (functorPairComparison F D A eD eA).hom ≫ snd D' A' = F.map (snd D A) ≫ eA.hom := by
  simp only [functorPairComparison, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso_hom]
  rw [Category.assoc, tensorHom_snd, ← Category.assoc, Functor.OplaxMonoidal.δ_snd]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairComparison
