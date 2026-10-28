import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartSectionEpi
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechCokernel
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal

/-! # Chart Ext Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartExtVanishing.AffineChartExtVanishing

noncomputable section

/-! The actual differential-form sheaves have vanishing positive coefficient Ext on any affine chart over a rational base. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "J" => Opens.grothendieckTopology X.left

abbrev sections : V ⥤ ModuleCat R :=
  sheafToPresheaf J (ModuleCat R) ⋙ (CategoryTheory.evaluation _ _).obj (op ⊤)

instance sections_additive : (sections R X).Additive where
  map_add := by intros; rfl

instance sections_preservesLimits : PreservesLimits (sections R X) := by
  change PreservesLimits (sheafToPresheaf J (ModuleCat R) ⋙
    (CategoryTheory.evaluation _ _).obj (op ⊤))
  infer_instance

theorem cycles_acyclic (F : V) (hF : CechAcyclic.AffineCechAcyclic.Acyclic R X F)
    (I : InjectiveResolution F) (n : ℕ) :
    CechAcyclic.AffineCechAcyclic.Acyclic R X (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.cycle I n) := by
  induction n with
  | zero => exact CechAcyclic.AffineCechAcyclic.of_iso R X hF (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.augmentationIso I)
  | succ n ih =>
    exact CechCokernel.AffineCechAcyclic.cokernel R X (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.shortComplex I n)
      (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.shortExact I n) ih

theorem cycle_section_lift (F : V) (I : InjectiveResolution F) (n : ℕ)
    (x : (I.cocomplex.X n).obj.obj (op ⊤))
    (hx : (I.cocomplex.d n (n + 1)).hom.app (op ⊤) x = 0) :
    ∃ c : (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.cycle I n).obj.obj (op ⊤),
      (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.inclusion I n).hom.app (op ⊤) c = x := by
  let K := ShortComplex.mk (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.inclusion I n) (I.cocomplex.d n (n + 1))
    (kernel.condition (I.cocomplex.d n (n + 1)))
  have hK : K.Exact := ShortComplex.kernelSequence_exact (I.cocomplex.d n (n + 1))
  have : Mono K.f := by change Mono (kernel.ι (I.cocomplex.d n (n + 1))); infer_instance
  have he := hK.map_of_mono_of_preservesKernel (sections R X) inferInstance inferInstance
  exact (ShortComplex.moduleCat_exact_iff (K.map (sections R X))).mp he x hx

variable [IsAffine X.left] [Algebra ℚ Γ(X.left, ⊤)]

theorem evaluated_exactAt (F : V) (hF : CechAcyclic.AffineCechAcyclic.Acyclic R X F)
    (I : InjectiveResolution F) (n : ℕ) :
    (((sections R X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change ((I.cocomplex.sc' n (n + 1) (n + 2)).map (sections R X)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨c, hc⟩ := cycle_section_lift R X F I (n + 1) x hx
  have hGood := cycles_acyclic R X F hF I n
  have hp := ChartSectionEpi.AffineCechAcyclic.affine_section_epi R X (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.shortComplex I n)
    (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.shortExact I n) hGood
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.shortComplex I n).g.hom.app (op ⊤))).mp hp c
  refine ⟨y, ?_⟩
  have hfac := congrArg (fun f => f.hom.app (op ⊤) y) (AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.projection_inclusion I n)
  exact hfac.symm.trans
    ((congrArg ((AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle.InjectiveCycleTower.inclusion I (n + 1)).hom.app (op ⊤)) hy).trans hc)

local instance : HasExt.{1} V := HasExt.standard _

theorem ext_subsingleton (F : V) (hF : CechAcyclic.AffineCechAcyclic.Acyclic R X F) (n : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F (n + 1)) := by
  let I : InjectiveResolution F := injectiveResolution F
  let e := (NatIso.mapHomologicalComplex
    (Sheaf.ΓNatIsoSheafSections J (ModuleCat R) (isTerminalTop : IsTerminal (⊤ : X.left.Opens)))
      (.up ℕ)).app I.cocomplex
  have hI := (evaluated_exactAt R X F hF I n).of_iso e.symm
  have hz : ∀ α : Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) F (n + 1), α = 0 :=
    @AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal.SheafGlobalExtVanishing.ext_eq_zero.{0, 0, 0, 1} _ _ J R _ _ _
      (inferInstanceAs (HasExt.{1} V)) F I n hI
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

theorem forms_ext_subsingleton (j n : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j) (n + 1)) :=
  ext_subsingleton R X _ (CechAcyclic.AffineCechAcyclic.forms R X j) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.ChartExtVanishing.AffineChartExtVanishing
