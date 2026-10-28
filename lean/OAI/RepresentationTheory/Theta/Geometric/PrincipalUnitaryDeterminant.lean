import OAI.RepresentationTheory.Theta.Geometric.LatticeDeterminantCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELEquiv
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Principal Unitary Determinant -/

namespace OAI.RepresentationTheory.Theta.Geometric.PrincipalUnitaryDeterminant

noncomputable section

section

/-! Level at least three suffices for determinant one on the original
full lattice. This removes any need to refine the public PEL level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem principal_unitary_determinant_one {E J : Type*} [Field E] [NumberField E]
    [NumberField.IsCMField E] [Fintype J] (b : E) (hb : b ≠ 0)
    (L : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (basis : Module.Basis J ℤ L)
    (hspan : Submodule.span ℚ (L : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤)
    (N : ℕ) (hN : 3 ≤ N) (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hh : ∀ x y, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b (g x) (g y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)
    (hc : ∀ x ∈ L, ∃ y ∈ L, g x - x = N • y) : LinearMap.det g.toLinearMap = 1 := by
  obtain ⟨a, ha, he⟩ := LatticeDeterminantCongruence.lattice_determinant_congruence L basis hspan g N (by omega) hc
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence.norm_one_integral_congruence_eq_one _ a ha N hN he (AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitaryDeterminant.unitary_det_norm_one b hb g hh)

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    {C : Reference.PolarizationConstruction.ReferencePolarizationConstruction p} {C' : Reference.PolarizationConstruction.ReferencePolarizationConstruction p'}
    {level : ℕ} [NeZero level] (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level))

theorem referencePELFieldEquiv_determinant (hlevel : 3 ≤ level) :
    LinearMap.det (Reference.PELEquiv.referencePELFieldEquiv e).toLinearMap = 1 := by
  have hb : P.b ≠ 0 := hP.2.2.1
  have hspan : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
    exact h.2.1
  apply principal_unitary_determinant_one P.b hb P.lattice (P.referenceBasis hP) hspan
    level hlevel (Reference.PELEquiv.referencePELFieldEquiv e) (Reference.PELEquiv.referencePELFieldEquiv_hermitian e)
  intro v hv
  exact Reference.PELEquiv.referencePELFieldEquiv_level e ⟨v, hv⟩

end

/-! Every actual reference PEL isomorphism at level at least three
determines a genuine element of the original rational special unitary
matrix group, with its exact lattice action and level congruence. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DeterminantCongruence

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    {C : Reference.PolarizationConstruction.ReferencePolarizationConstruction p} {C' : Reference.PolarizationConstruction.ReferencePolarizationConstruction p'}
    {level : ℕ} [NeZero level] (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level))
    (hlevel : 3 ≤ level)

def referencePELRationalSU : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b := by
  refine ⟨⟨LinearMap.toMatrix' (Reference.PELEquiv.referencePELFieldEquiv e).toLinearMap, ?_⟩, ?_⟩
  · rw [LinearMap.det_toMatrix', referencePELFieldEquiv_determinant e hlevel]
  · intro x y
    change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b
        (Matrix.toLin' (LinearMap.toMatrix' (Reference.PELEquiv.referencePELFieldEquiv e).toLinearMap) x)
        (Matrix.toLin' (LinearMap.toMatrix' (Reference.PELEquiv.referencePELFieldEquiv e).toLinearMap) y) =
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y
    rw [Matrix.toLin'_toMatrix']
    exact Reference.PELEquiv.referencePELFieldEquiv_hermitian e x y

theorem referencePELRationalSU_linear :
    Matrix.SpecialLinearGroup.toLin' (referencePELRationalSU e hlevel).val = Reference.PELEquiv.referencePELFieldEquiv e := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix' (Reference.PELEquiv.referencePELFieldEquiv e).toLinearMap) x

theorem referencePELRationalSU_lattice (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    x ∈ P.lattice ↔ Matrix.SpecialLinearGroup.toLin' (referencePELRationalSU e hlevel).val x ∈ P.lattice := by
  rw [referencePELRationalSU_linear]
  exact Reference.PELEquiv.referencePELFieldEquiv_lattice e x

theorem referencePELRationalSU_level (x : P.lattice) :
    ∃ y ∈ P.lattice,
      Matrix.SpecialLinearGroup.toLin' (referencePELRationalSU e hlevel).val x.val - x.val = level • y := by
  rw [referencePELRationalSU_linear]
  exact Reference.PELEquiv.referencePELFieldEquiv_level e x

end

end OAI.RepresentationTheory.Theta.Geometric.PrincipalUnitaryDeterminant
