import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SectionIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # Injective Frame Cech Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveFrameCechExactness

noncomputable section

/-! A genuine covering family has no positive Čech cohomology with
injective sheaf coefficients. The free sheaf resolution and injectivity
produce an actual cochain primitive. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R]
  (J : GrothendieckTopology C)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)

include hcover in
omit [HasBinaryProducts C] in
theorem chain_exact (n : ℕ) :
    (CoveringPresentationResolution.complex J R F).ExactAt (n + 1) := by
  let a := CoveringPresentationResolution.augmentation J R F
  let h : QuasiIso a := CoveringPresentationResolution.augmentation_quasiIso J R F hcover
  let : QuasiIsoAt a (n + 1) := h.quasiIsoAt (n + 1)
  exact (exactAt_iff_of_quasiIsoAt a (n + 1)).mpr
    (ChainComplex.exactAt_succ_single_obj _ n)

variable (H : Sheaf J (ModuleCat.{max u v} R)) [Injective H]

include hcover in
theorem boundary (n : ℕ) (x : (FrameCech.Differential.complex F R H.obj).X (n + 1))
    (hx : (FrameCech.Differential.complex F R H.obj).d (n + 1) (n + 2) x = 0) :
    ∃ y : (FrameCech.Differential.complex F R H.obj).X n,
      (FrameCech.Differential.complex F R H.obj).d n (n + 1) y = x := by
  let P := CoveringPresentationResolution.complex J R F
  let K := FrameCech.Differential.complex F R H.obj
  let e := FrameCech.SectionIso.component F R J H
  let a : P.X (n + 1) ⟶ H := (e (n + 1)).inv x
  have ha : (e (n + 1)).hom a = x := by
    exact (e (n + 1)).inv_hom_id_apply x
  have hda : P.d (n + 2) (n + 1) ≫ a = 0 := by
    apply (e (n + 2)).toLinearEquiv.injective
    change (e (n + 2)).hom (P.d (n + 2) (n + 1) ≫ a) = (e (n + 2)).hom 0
    rw [map_zero]
    have he := congrArg (fun f => f a) (FrameCech.SectionIso.comm F R J H (n + 1))
    change K.d (n + 1) (n + 2) ((e (n + 1)).hom a) =
      (e (n + 2)).hom (P.d (n + 2) (n + 1) ≫ a) at he
    rw [ha, hx] at he
    exact he.symm
  have hS : (P.sc' (n + 2) (n + 1) n).Exact :=
    (HomologicalComplex.exactAt_iff' P (n + 2) (n + 1) n (by simp) (by simp)).mp
      (chain_exact F R J hcover n)
  let b : P.X n ⟶ H := hS.descToInjective a hda
  refine ⟨(e n).hom b, ?_⟩
  have he := congrArg (fun f => f b) (FrameCech.SectionIso.comm F R J H n)
  change K.d n (n + 1) ((e n).hom b) = (e (n + 1)).hom (P.d (n + 1) n ≫ b) at he
  have hb : P.d (n + 1) n ≫ b = a := hS.comp_descToInjective a hda
  exact he.trans ((congrArg (fun t : P.X (n + 1) ⟶ H => (e (n + 1)).hom t) hb).trans ha)

def coordinatesEquiv (n : ℕ) : (FrameCech.Differential.complex F R H.obj).X n ≃ₗ[R]
    (∀ t : Fin (n + 1) → ι,
      H.obj.obj (op (Presentation.TupleProducts.family F n t))) :=
  (ModuleCat.piIsoPi.{max u v, v, max u v}
    (fun t => H.obj.obj (op (Presentation.TupleProducts.family F n t)))).toLinearEquiv

omit [Injective H] in
theorem coordinatesEquiv_apply (n : ℕ)
    (x : (FrameCech.Differential.complex F R H.obj).X n) (t : Fin (n + 1) → ι) :
    coordinatesEquiv F R J H n x t = FrameCech.Differential.coordinate F R H.obj n t x :=
  congrArg (fun f => f x) (ModuleCat.piIsoPi_hom_ker_subtype.{max u v, v, max u v}
    (fun t => H.obj.obj (op (Presentation.TupleProducts.family F n t))) t)

include hcover in
theorem boundary_coordinates (n : ℕ)
    (x : ∀ t : Fin (n + 2) → ι,
      H.obj.obj (op (Presentation.TupleProducts.family F (n + 1) t)))
    (hx : ∀ t : Fin (n + 3) → ι,
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
          (x (t ∘ i.succAbove))) = 0) :
    ∃ y : ∀ t : Fin (n + 1) → ι,
      H.obj.obj (op (Presentation.TupleProducts.family F n t)),
      ∀ t : Fin (n + 2) → ι,
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op
            (y (t ∘ i.succAbove))) = x t := by
  let c := (coordinatesEquiv F R J H (n + 1)).symm x
  have hc : ∀ t, FrameCech.Differential.coordinate F R H.obj (n + 1) t c = x t := by
    intro t
    rw [← coordinatesEquiv_apply]
    exact congrFun ((coordinatesEquiv F R J H (n + 1)).apply_symm_apply x) t
  have hdc : (FrameCech.Differential.complex F R H.obj).d (n + 1) (n + 2) c = 0 := by
    apply (coordinatesEquiv F R J H (n + 2)).injective
    ext t
    rw [coordinatesEquiv_apply, map_zero, Pi.zero_apply,
      FrameCech.Differential.coordinates]
    simp only [hc]
    exact hx t
  obtain ⟨b, hb⟩ := boundary F R J hcover H n c hdc
  refine ⟨coordinatesEquiv F R J H n b, fun t => ?_⟩
  simp only [coordinatesEquiv_apply]
  rw [← FrameCech.Differential.coordinates, hb, hc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveFrameCechExactness
