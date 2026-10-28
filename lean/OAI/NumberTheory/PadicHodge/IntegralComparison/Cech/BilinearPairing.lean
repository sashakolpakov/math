import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.BilinearCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Bilinear Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing

noncomputable section

/-! Natural presheaf pairings induce the actual product pairing on
the categorical products in a Čech cosimplicial module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t r

variable {R : Type r} [CommRing R]

section Products

variable {ι : Type w} (A B C : ι → ModuleCat.{max w t} R)
  (μ : ∀ i, A i →ₗ[R] B i →ₗ[R] C i)

def productPairing : (∏ᶜ A : ModuleCat.{max w t} R) →ₗ[R]
    (∏ᶜ B : ModuleCat.{max w t} R) →ₗ[R] (∏ᶜ C : ModuleCat.{max w t} R) :=
  LinearMap.mk₂ R
    (fun x y => (ModuleCat.piIsoPi C).inv (fun i => μ i (Pi.π A i x) (Pi.π B i y)))
    (fun x x' y => by
      rw [← map_add]
      congr 1
      funext i
      simp only [Pi.add_apply, map_add, LinearMap.add_apply])
    (fun a x y => by
      rw [← map_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply])
    (fun x y y' => by
      rw [← map_add]
      congr 1
      funext i
      simp only [Pi.add_apply, map_add])
    (fun a x y => by
      rw [← map_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_smul])

theorem projection_productPairing (i : ι)
    (x : (∏ᶜ A : ModuleCat.{max w t} R)) (y : (∏ᶜ B : ModuleCat.{max w t} R)) :
    Pi.π C i (productPairing A B C μ x y) = μ i (Pi.π A i x) (Pi.π B i y) :=
  ConcreteCategory.congr_hom (ModuleCat.piIsoPi_inv_kernel_ι C i) _

end Products

variable {D : Type u} [Category.{v} D]
  (N : SimplicialObject (FormalCoproduct.{w} D))
  (P Q T : Dᵒᵖ ⥤ ModuleCat.{max w t} R)

def cosimplicial (P : Dᵒᵖ ⥤ ModuleCat.{max w t} R) :
    CosimplicialObject (ModuleCat.{max w t} R) :=
  (FormalCoproduct.cosimplicialObjectFunctor N).obj P

def projection (n : SimplexCategory) (i : (N.obj (op n)).I) :
    (cosimplicial N P).obj n →ₗ[R] P.obj (op ((N.obj (op n)).obj i)) :=
  (Pi.π (fun j => P.obj (op ((N.obj (op n)).obj j))) i).hom

theorem projection_map {n m : SimplexCategory} (f : n ⟶ m) (i : (N.obj (op m)).I)
    (x : (cosimplicial N P).obj n) :
    projection N P m i ((cosimplicial N P).map f x) =
      P.map ((N.map f.op).φ i).op (projection N P n ((N.map f.op).f i) x) := by
  change Pi.π (fun j => P.obj (op ((N.obj (op m)).obj j))) i (Pi.lift
    (fun j => Pi.π (fun k => P.obj (op ((N.obj (op n)).obj k))) ((N.map f.op).f j) ≫
      P.map ((N.map f.op).φ j).op) x) = _
  exact ConcreteCategory.congr_hom (Pi.lift_comp_π _ i) x

variable (μ : ∀ U : Dᵒᵖ, P.obj U →ₗ[R] Q.obj U →ₗ[R] T.obj U)
  (hμ : ∀ {U V : Dᵒᵖ} (f : U ⟶ V) (x : P.obj U) (y : Q.obj U),
    T.map f (μ U x y) = μ V (P.map f x) (Q.map f y))

def pairing (n : SimplexCategory) :
    (cosimplicial N P).obj n →ₗ[R] (cosimplicial N Q).obj n →ₗ[R] (cosimplicial N T).obj n :=
  productPairing
    (fun i => P.obj (op ((N.obj (op n)).obj i)))
    (fun i => Q.obj (op ((N.obj (op n)).obj i)))
    (fun i => T.obj (op ((N.obj (op n)).obj i)))
    (fun i => μ (op ((N.obj (op n)).obj i)))

theorem projection_pairing (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (cosimplicial N P).obj n) (y : (cosimplicial N Q).obj n) :
    projection N T n i (pairing N P Q T μ n x y) =
      μ (op ((N.obj (op n)).obj i)) (projection N P n i x) (projection N Q n i y) :=
  projection_productPairing _ _ _ _ i x y

include hμ in
theorem pairing_natural {n m : SimplexCategory} (f : n ⟶ m)
    (x : (cosimplicial N P).obj n) (y : (cosimplicial N Q).obj n) :
    (cosimplicial N T).map f (pairing N P Q T μ n x y) =
      pairing N P Q T μ m ((cosimplicial N P).map f x) ((cosimplicial N Q).map f y) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => T.obj (op ((N.obj (op m)).obj i)))
  intro i
  change projection N T m i _ = projection N T m i _
  rw [projection_map, projection_pairing, projection_pairing,
    projection_map, projection_map, hμ]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing
