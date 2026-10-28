import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Differential
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionDifferential
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Section Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SectionIso

noncomputable section

/-! The actual dual of the frame presentation resolution is the native frame Čech cochain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

variable (H : Sheaf J (ModuleCat.{max u v} R))

def homComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (((linearYoneda R (Sheaf J (ModuleCat.{max u v} R))).obj H).mapHomologicalComplex (.up ℕ)).obj
    (CoveringPresentationResolution.complex J R F).op

def component (n : ℕ) : (homComplex F R J H).X n ≅ (Differential.complex F R H.obj).X n :=
  ((Presentation.ResolutionCoordinates.sheaf F R n J H).trans
    (ModuleCat.piIsoPi.{max u v, v, max u v}
      (fun t => H.obj.obj (op (Presentation.TupleProducts.family F n t)))).symm.toLinearEquiv).toModuleIso

theorem component_coordinate (n : ℕ) (a : (CoveringPresentationResolution.complex J R F).X n ⟶ H)
    (t : Fin (n + 1) → ι) :
    Differential.coordinate F R H.obj n t ((component F R J H n).hom a) =
      Presentation.ResolutionCoordinates.sheaf F R n J H a t :=
  congrArg (fun f => f (Presentation.ResolutionCoordinates.sheaf F R n J H a))
    (ModuleCat.piIsoPi_inv_kernel_ι.{max u v, v, max u v}
      (fun t => H.obj.obj (op (Presentation.TupleProducts.family F n t))) t)

theorem comm (n : ℕ) : (component F R J H n).hom ≫ (Differential.complex F R H.obj).d n (n + 1) =
    (homComplex F R J H).d n (n + 1) ≫ (component F R J H (n + 1)).hom := by
  apply Pi.hom_ext
  intro t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (CoveringPresentationResolution.complex J R F).X n ⟶ H at a
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun (i : Fin (n + 2)) _ => congrArg
      (fun x => (-1 : ℤ) ^ (i : ℕ) • H.obj.map (Presentation.ResolutionFaceMaps.productMap F i.succAbove t).op x)
        (component_coordinate F R J H n a (t ∘ i.succAbove)))
  exact (Differential.coordinates F R H.obj n t ((component F R J H n).hom a)).trans
    (hs.trans ((Presentation.ResolutionDifferential.coordinates F R J H n a t).symm.trans
      (component_coordinate F R J H (n + 1)
        ((CoveringPresentationResolution.complex J R F).d (n + 1) n ≫ a) t).symm))

def iso : homComplex F R J H ≅ Differential.complex F R H.obj :=
  HomologicalComplex.Hom.isoOfComponents (component F R J H) (by
    intro i j hij
    have h : i + 1 = j := hij
    subst j
    exact comm F R J H i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SectionIso
