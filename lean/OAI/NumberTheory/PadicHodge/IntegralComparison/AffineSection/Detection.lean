import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Isomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

/-! # Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Detection

noncomputable section

/-! Isomorphisms of quasicoherent module sheaves are detected by their
actual module sections on an affine open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

theorem spec {R : Type u} [CommRing R]
    {M N : (Spec (CommRingCat.of R)).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) [IsIso (Affine.InternalHom.sections.map a)] : IsIso a := by
  let e := Isomorphism.iso M N (asIso (Affine.InternalHom.sections.map a))
  have he : a = e.hom := by
    apply (Affine.InternalHom.homEquiv M N).injective
    calc
      _ = Affine.InternalHom.sections.map a := Affine.InternalHom.homEquiv_apply M N a
      _ = Affine.InternalHom.sections.map e.hom :=
        (Isomorphism.sections_iso_hom M N
          (asIso (Affine.InternalHom.sections.map a))).symm
      _ = _ := (Affine.InternalHom.homEquiv_apply M N e.hom).symm
  rw [he]
  infer_instance

theorem open_restrict {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsIso ((Affine.ModuleExactSections.sections U).map a)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) := by
  let G := AffineOpen.InternalHom.chartFunctor U hU
  let : (G.obj M).IsQuasicoherent := AffineOpen.InternalHom.chart_quasicoherent U hU M
  let : (G.obj N).IsQuasicoherent := AffineOpen.InternalHom.chart_quasicoherent U hU N
  have hS : IsIso ((AffineOpen.InternalHom.sections U hU).map a) :=
    (NatIso.isIso_map_iff (AffineOpen.LinearHom.sectionsIso U hU) a).mp inferInstance
  let : IsIso (Affine.InternalHom.sections.map (G.map a)) := hS
  let : IsIso (G.map a) := spec (G.map a)
  let F := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  let : F.IsEquivalence := inferInstanceAs
    (Scheme.Modules.restrictFunctor hU.isoSpec.symm.hom).IsEquivalence
  let : IsIso (F.map ((Scheme.Modules.restrictFunctor U.ι).map a)) :=
    inferInstanceAs (IsIso (G.map a))
  exact isIso_of_reflects_iso ((Scheme.Modules.restrictFunctor U.ι).map a) F

theorem cover {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) (hAffine : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, IsIso ((Affine.ModuleExactSections.sections (U i)).map a)) : IsIso a := by
  apply AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isIso_of_isIso_restrict a U hU
  intro i
  let := h i
  exact open_restrict a (U i) (hAffine i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Detection
