import OAI.NumberTheory.PadicHodge.IntegralComparison.NonpositiveProjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Hom
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Projective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ProjectiveResolution

noncomputable section

/-! The genuine scalar-cone Koszul complex as a projective resolution
of its original quotient, and comparison with any other projective
resolution of that quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (rs : List R)

open OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul

instance supported : (RegularSequenceKoszul.complex M rs).IsStrictlySupported NonpositiveProjectiveResolution.shape where
  isZero i hi := RegularSequenceKoszul.term_isZero M rs i (Or.inr
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).mp hi))

instance projective_term [Module.Free R M] (n : ℕ) :
    Projective ((RegularSequenceKoszul.complex M rs).X (NonpositiveProjectiveResolution.shape.f n)) := by
  let := RegularSequenceKoszul.term_free M rs (NonpositiveProjectiveResolution.shape.f n)
  infer_instance

def resolution [Module.Free R M] (hreg : RingTheory.Sequence.IsWeaklyRegular M rs) :
    ProjectiveResolution (RegularSequenceKoszul.quotient M rs) := by
  let ε := Classical.choose (RegularSequenceKoszul.exists_augmentation M rs hreg)
  letI : QuasiIso ε := Classical.choose_spec (RegularSequenceKoszul.exists_augmentation M rs hreg)
  exact NonpositiveProjectiveResolution.ofComplex (RegularSequenceKoszul.quotient M rs) (RegularSequenceKoszul.complex M rs) ε

def homologyIso [Module.Free R M] (hreg : RingTheory.Sequence.IsWeaklyRegular M rs)
    (P : ProjectiveResolution (RegularSequenceKoszul.quotient M rs)) (N : ModuleCat.{u} R) (n : ℕ) :
    ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj P.complex.op).homology n ≅
    ((((linearYoneda R (ModuleCat R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ).symm).obj (resolution M rs hreg).complex.op).homology n :=
  IntegralComparison.ProjectiveResolution.Hom.Comparison.moduleHomologyIso P (resolution M rs hreg) N n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ProjectiveResolution
