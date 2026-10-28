import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulResolution

/-! # Koszul Basis Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulBasisResolution

noncomputable section

/-! The actual exterior Koszul resolution in an arbitrary finite basis,
with its literal quotient augmentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def complexIso (s : Module.Dual R V) (t : Module.Dual R W)
    (e : V ≃ₗ[R] W) (h : t.comp e.toLinearMap = s) :
    KoszulComplex.complex R V s ≅ KoszulComplex.complex R W t where
  hom := KoszulComplex.map R V W s t e.toLinearMap h
  inv := KoszulComplex.map R W V t s e.symm.toLinearMap (by
    ext x
    exact (LinearMap.congr_fun h (e.symm x)).symm.trans (by simp))
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    change (exteriorPower.map n e.symm.toLinearMap).comp
      (exteriorPower.map n e.toLinearMap) = LinearMap.id
    rw [← exteriorPower.map_comp]
    simp
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    change (exteriorPower.map n e.toLinearMap).comp
      (exteriorPower.map n e.symm.toLinearMap) = LinearMap.id
    rw [← exteriorPower.map_comp]
    simp

variable {n : ℕ} (b : Module.Basis (Fin n) R V) (s : Module.Dual R V)

theorem equation_basis : s.comp b.equivFun.symm.toLinearMap =
    Koszul.GeneratorMatrix.equation R (fun i => s (b i)) := by
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  simp [LinearMap.comp_apply, Pi.basisFun_apply, Module.Basis.equivFun_symm_apply,
    Koszul.GeneratorMatrix.equation_apply, Pi.single_apply]

def basisIso : Koszul.OrientedTopCohomology.koszul R (fun i => s (b i)) ≅
    KoszulComplex.complex R V s :=
  complexIso R _ s b.equivFun.symm (equation_basis R b s)

abbrev ideal : Ideal R := Koszul.OrientedTopCohomology.ideal R (fun i => s (b i))

def resolution (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (fun i => s (b i)))) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ ideal R b s)) where
  complex := KoszulComplex.complex R V s
  projective k := Projective.of_iso
    ((HomologicalComplex.eval _ _ k).mapIso (basisIso R b s))
      (KoszulResolution.term_projective R (fun i => s (b i)) k)
  π := (basisIso R b s).inv ≫ (KoszulResolution.resolution R _ hreg).π
  quasiIso := by
    have := (KoszulResolution.resolution R _ hreg).quasiIso
    exact quasiIso_comp _ _

theorem resolution_π_zero
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (fun i => s (b i)))) :
    (resolution R b s hreg).π.f 0 =
      ModuleCat.ofHom ((ideal R b s).mkQ.comp (exteriorPower.zeroEquiv R V).toLinearMap) := by
  rw [show (resolution R b s hreg).π.f 0 = (basisIso R b s).inv.f 0 ≫
      (KoszulResolution.resolution R _ hreg).π.f 0 from rfl,
    KoszulResolution.resolution_π_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (ideal R b s).mkQ (exteriorPower.zeroEquiv R _
    (exteriorPower.map 0 b.equivFun.toLinearMap x)) =
      (ideal R b s).mkQ (exteriorPower.zeroEquiv R V x)
  exact congrArg (ideal R b s).mkQ
    (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality b.equivFun.toLinearMap) x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulBasisResolution
