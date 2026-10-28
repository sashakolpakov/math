import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalizedScalar
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Pi Extension -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtension

noncomputable section

/-! Scalar extension of a finite section family, in actual function
coordinates, with its value on every canonical tensor generator. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace Construction.FinitePiExtension

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable {I : Type u} [Finite I] (P : I → ModuleCat.{u} R) (Q : I → ModuleCat.{u} S)
variable (e : ∀ i, (ModuleCat.extendScalars f).obj (P i) ≅ Q i)

def iso : (ModuleCat.extendScalars f).obj (ModuleCat.of R (∀ i, P i)) ≅
    ModuleCat.of S (∀ i, Q i) :=
  (ModuleCat.extendScalars f).mapIso (ModuleCat.piIsoPi P).symm ≪≫
    asIso (piComparison (ModuleCat.extendScalars f) P) ≪≫
      Pi.mapIso e ≪≫ ModuleCat.piIsoPi Q

theorem component (i : I) :
    (iso f P Q e).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (ModuleCat.extendScalars f).map (ModuleCat.ofHom (LinearMap.proj i)) ≫ (e i).hom := by
  simp only [iso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, Pi.mapIso_hom_π,
    piComparison_comp_π_assoc, ← Functor.map_comp_assoc, ModuleCat.piIsoPi_inv_kernel_ι]

theorem one (s : ∀ i, P i) (i : I) :
    (iso f P Q e).hom ((1 : S) ⊗ₜ[R,f] s) i = (e i).hom ((1 : S) ⊗ₜ[R,f] (s i)) := by
  exact ConcreteCategory.congr_hom (component f P Q e i) ((1 : S) ⊗ₜ[R,f] s)

def data (v : ∀ i, P i → Q i) (d : ∀ i, NormalizedScalar.Construction.NormalizedScalarIso.Data f (v i)) :
    NormalizedScalar.Construction.NormalizedScalarIso.Data f (B := ModuleCat.of S (∀ i, Q i))
      (fun s : ModuleCat.of R (∀ i, P i) => fun i => v i (s i)) :=
  ⟨iso f P Q (fun i => (d i).val), fun s => funext fun i =>
    (one f P Q (fun i => (d i).val) s i).trans ((d i).property (s i))⟩

end Construction.FinitePiExtension

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PiExtension
