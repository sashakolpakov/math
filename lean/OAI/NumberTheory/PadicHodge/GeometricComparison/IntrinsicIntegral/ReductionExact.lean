import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafLocal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralSheafRegular

/-! # Reduction Exact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionExact.IntrinsicIntegralReductionExact

noncomputable section

/-! The actual geometric reduction map yields short exact sequences of the first two form sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf.IntrinsicIntegralReductionPresheaf

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

theorem target_scalar_zero (n : ℕ) (r : R) (hr : algebraMap R S r = 0) :
    r • 𝟙 (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.target R S X Y f n) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  let M := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y n).obj ((TopologicalSpace.Opens.map f.base).op.obj U)
  let : Module S ((ReductionPresheaf.IntrinsicIntegralReductionPresheaf.target R S X Y f n).obj U) := M.isModule
  change (algebraMap R S r) • (ω : M) = 0
  rw [hr, zero_smul]

def sequence (n : ℕ) (r : R) (hr : algebraMap R S r = 0) :
    ShortComplex (X.left.Opensᵒᵖ ⥤ ModuleCat R) :=
  ShortComplex.mk (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n))
    (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n) (by
      rw [Linear.smul_comp, Category.id_comp]
      have hh := congrArg (fun g => ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n ≫ g)
        (target_scalar_zero R S X Y f n r hr)
      simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using hh)

variable (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hS : Function.Surjective (algebraMap R S))

include hp hS in
theorem locallySurjective (n : ℕ) (hn : n ≤ 1) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.left)
      (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n) where
  imageSieve_mem {V} s := by
    intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
    refine ⟨W, homOfLE hWV, ?_, hxW⟩
    exact ReductionPresheaf.IntrinsicIntegralReductionPresheaf.affine_surjective R S X Y f h hp W hW n hn hS
      ((ReductionPresheaf.IntrinsicIntegralReductionPresheaf.target R S X Y f n).map (homOfLE hWV).op s)

include hp hS in
theorem sheafification_exact (n : ℕ) (hn : n ≤ 1) (r : R) (hr : algebraMap R S r = 0)
    (hker : RingHom.ker (algebraMap R S) = Ideal.span {r}) :
    ((sequence R S X Y f h n r hr).map
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R))).Exact := by
  apply PresheafLocal.PresheafLocalExactness.sheafification_exact R
  intro V x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open x.property V.isOpen
  refine ⟨W, hWV, hxW, ?_⟩
  intro s hs
  exact (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.affine_zero_iff_divisible R S X Y f h hp W hW n hn hS r hker s).mp hs

include hp hS in
theorem sheafification_epi (n : ℕ) (hn : n ≤ 1) :
    Epi ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
      (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n)) := by
  let J := Opens.grothendieckTopology X.left
  let a := ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n
  let : Presheaf.IsLocallySurjective J a := locallySurjective R S X Y f h hp hS n hn
  let : Sheaf.IsLocallySurjective ((presheafToSheaf J (ModuleCat R)).map a) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J a).mpr inferInstance
  infer_instance

include hp hS in
theorem shortExact [Smooth X.hom] (n : ℕ) (hn : n ≤ 1) (r : R)
    (hr : algebraMap R S r = 0) (hker : RingHom.ker (algebraMap R S) = Ideal.span {r})
    (hreg : IsRegular r) :
    ((sequence R S X Y f h n r hr).map
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R))).ShortExact := by
  have hm := GeometricComparison.Smooth.IntegralSheafRegular.SmoothIntegralSheafRegular.monic R X n hn r hreg
  let : Mono ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
      (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n))) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact hm
  let := sheafification_epi R S X Y f h hp hS n hn
  let : Mono (((sequence R S X Y f h n r hr).map
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R))).f) := by
    change Mono ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
      (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)))
    infer_instance
  let : Epi (((sequence R S X Y f h n r hr).map
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R))).g) := by
    change Epi ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
      (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n))
    infer_instance
  exact ⟨sheafification_exact R S X Y f h hp hS n hn r hr hker⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionExact.IntrinsicIntegralReductionExact
