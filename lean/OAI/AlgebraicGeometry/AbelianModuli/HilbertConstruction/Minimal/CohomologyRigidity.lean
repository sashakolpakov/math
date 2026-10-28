import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroComplexHomologyMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ComplexRigidity

/-! # Cohomology Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.CohomologyRigidity.LocalSectionLifting

noncomputable section

/-! Injectivity on first fiber cohomology forces the minimal first differential to vanish. -/

open _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {S T : ShortComplex (ModuleCat.{u} R)}
    [Module.Finite R S.X₂] [Module.Finite R T.X₂] [Module.Free R T.X₂]

theorem first_differential_eq_zero_of_residue_homology_injective (φ : S ⟶ T)
    (hSf : S.f.hom.baseChange (IsLocalRing.ResidueField R) = 0)
    (hSg : S.g.hom.baseChange (IsLocalRing.ResidueField R) = 0)
    (hTg : T.g.hom.baseChange (IsLocalRing.ResidueField R) = 0)
    (hTf : T.f.hom = 0)
    (hH : Function.Injective (ShortComplex.homologyMap
      ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)).mapShortComplex.map φ))) :
    S.f.hom = 0 := by
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (IsLocalRing.ResidueField R)
  let φk := F.mapShortComplex.map φ
  have hmono : Mono (ShortComplex.homologyMap φk) :=
    (ModuleCat.mono_iff_injective _).mpr hH
  have hTf' : T.f.hom.baseChange (IsLocalRing.ResidueField R) = 0 := by
    rw [hTf, LinearMap.baseChange_zero]
  have hmid : Mono φk.τ₂ := ZeroComplexHomologyMap.LocalSectionLifting.zeroShortComplex_middle_mono φk
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_f_zero R (IsLocalRing.ResidueField R) S hSf)
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_g_zero R (IsLocalRing.ResidueField R) S hSg)
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_f_zero R (IsLocalRing.ResidueField R) T hTf')
    (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex_g_zero R (IsLocalRing.ResidueField R) T hTg)
  have hb : Function.Injective (φ.τ₂.hom.lTensor (IsLocalRing.ResidueField R)) :=
    (ModuleCat.mono_iff_injective φk.τ₂).mp hmid
  apply Local.ComplexRigidity.LocalSectionLifting.local_differential_eq_zero_of_detecting_map S.f.hom T.f.hom φ.τ₁.hom φ.τ₂.hom
  · exact (ModuleCat.hom_ext_iff.mp φ.comm₁₂).symm
  · exact hTf
  · exact hb

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.CohomologyRigidity.LocalSectionLifting
