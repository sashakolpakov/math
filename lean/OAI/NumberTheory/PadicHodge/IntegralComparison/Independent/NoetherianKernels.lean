import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.OpenGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineFiniteGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentKernels
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.NoetherianKernels

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def refinedGenerators {X : Scheme.{u}} (M : X.Modules) (U W : X.Opens)
    (hU : IsAffineOpen U) (hUW : U ≤ W) (G : (M.restrict W.ι).GeneratingSections) :
    (M.restrict hU.fromSpec).GeneratingSections := by
  let j := hU.isoSpec.inv ≫ X.homOfLE hUW
  have hj : j ≫ W.ι = hU.fromSpec := by
    dsimp [j]
    rw [Category.assoc, Scheme.homOfLE_ι, hU.isoSpec_inv_ι]
  let H := OpenGenerators.restrict j G
  let e := ((Scheme.Modules.restrictFunctorComp j W.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hj).app M
  exact SheafOfModules.GeneratingSections.equivOfIso e H

theorem refinedGenerators_finite {X : Scheme.{u}} (M : X.Modules) (U W : X.Opens)
    (hU : IsAffineOpen U) (hUW : U ≤ W) (G : (M.restrict W.ι).GeneratingSections)
    [hG : G.IsFiniteType] : (refinedGenerators M U W hU hUW G).IsFiniteType := by
  constructor
  exact hG.finite

theorem kernel_generators {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (U W : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ W)
    (G : (M.restrict W.ι).GeneratingSections) [G.IsFiniteType] :
    ∃ H : ((kernel f).restrict U.ι).GeneratingSections, H.IsFiniteType := by
  let R := Γ(X, U)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let GM := refinedGenerators M U W hU hUW G
  let : GM.IsFiniteType := refinedGenerators_finite M U W hU hUW G
  let : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (F.obj M)) :=
    AffineFiniteGenerators.finite_of_generators R (F.obj M) GM
  let : (kernel (F.map f)).IsQuasicoherent := AffineKernels.quasicoherent (F.map f)
  let : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (kernel (F.map f))) :=
    AffineFiniteGenerators.kernel_sections_finite R (F.obj M) (F.map f)
  obtain ⟨GK, hGK⟩ := AffineFiniteGenerators.generators R (kernel (F.map f))
  let : PreservesLimit (parallelPair f 0) F :=
    QuasicoherentKernels.restrict_preservesKernel hU.fromSpec f
  let e := PreservesKernel.iso F f
  let Gspec := SheafOfModules.GeneratingSections.equivOfIso e.symm GK
  let : Gspec.IsFiniteType := ⟨hGK.finite⟩
  exact ⟨AffineOpen.ModuleGenerators.generatingSections (kernel f) U hU Gspec,
    AffineOpen.ModuleGenerators.generatingSections_finite (kernel f) U hU Gspec⟩

theorem finiteType {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] (f : M ⟶ N) :
    (kernel f).IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hcover : IsOpenCover q.X := (Opens.coversTop_iff X q.X).mp q.coversTop
  choose κ hκ heq using fun i : q.I =>
    Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (q.X i)
  let ι := (i : q.I) × κ i
  let U : ι → X.Opens := fun t => t.2.1
  have hU : IsOpenCover U := by
    change (⨆ t : ι, t.2.1) = ⊤
    rw [iSup_sigma]
    simpa only [IsOpenCover, ← sSup_eq_iSup', ← heq] using hcover
  have hgen : ∀ t : ι, ∃ H : ((kernel f).restrict (U t).ι).GeneratingSections,
      H.IsFiniteType := by
    intro t
    have ht : IsAffineOpen (U t) := hκ t.1 t.2.2
    have hle : U t ≤ q.X t.1 := by
      rw [heq]
      exact le_sSup t.2.2
    let G := OpenGenerators.fromOver M (q.X t.1) (q.generators t.1)
    let : (q.generators t.1).IsFiniteType := hq.isFiniteType t.1
    let : G.IsFiniteType :=
      OpenGenerators.fromOver_finite M (q.X t.1) (q.generators t.1)
    exact kernel_generators f (U t) (q.X t.1) ht hle G
  choose G hG using hgen
  exact OpenGenerators.finiteType_of_open_generators (kernel f) U hU G hG

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.NoetherianKernels
