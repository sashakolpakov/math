import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.CohomologyCup
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientCoordinates

/-! # Assembly Coefficient Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyCoefficientCup

noncomputable section

/-! Cup coordinates for the literal coefficient comparison of an
assembled complex-valued Čech diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v r s a b
variable {C : Type u} [Category.{v} C]
  {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  (F : ModuleCat.{a} R ⥤ ModuleCat.{b} S) [F.Additive]
  (η : ∀ M : ModuleCat.{a} R, M →+ F.obj M)
  (hη : ∀ {M N : ModuleCat.{a} R} (f : M ⟶ N) (x : M),
    F.map f (η M x) = η N (f x))
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (hE : ∀ n, Finite (E.obj (op n)).I)
  (P : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{a} R) ℕ)

local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) P
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ)
  (P ⋙ Functor.mapHomologicalComplex F (ComplexShape.up ℕ))

def map (n : ℕ) :=
  ((GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom.f n).hom.toAddMonoidHom.comp
    (η ((Presheaf.TotalCup.CechProduct.total E K).X n))

theorem map_eq (n : ℕ) :
    AssemblyCoefficientCup.map F η E hE P n = CechCoefficient.TotalCup.map F η E hE K n := by
  unfold AssemblyCoefficientCup.map CechCoefficient.TotalCup.map
  rw [GeometricComparison.CechAssembly.CoefficientCoordinates.CechAssemblyCoefficientCoordinates.hom]
  rfl

variable
  (μ : ∀ p q U, ((P.obj U).X p) →ₗ[R] ((P.obj U).X q) →ₗ[R] ((P.obj U).X (p+q)))
  (ν : ∀ p q U, F.obj ((P.obj U).X p) →ₗ[S] F.obj ((P.obj U).X q) →ₗ[S]
    F.obj ((P.obj U).X (p+q)))
  (hprod : ∀ p q U (x : (P.obj U).X p) (y : (P.obj U).X q),
    η ((P.obj U).X (p+q)) (μ p q U x y) =
      ν p q U (η ((P.obj U).X p) x) (η ((P.obj U).X q) y))

include hη hprod in
theorem map_cup (i j : ℕ) (x : (Presheaf.TotalCup.CechProduct.total E K).X i) (y : (Presheaf.TotalCup.CechProduct.total E K).X j) :
    AssemblyCoefficientCup.map F η E hE P (i+j) (Presheaf.TotalCup.CechProduct.totalCup E K μ i j x y) =
      Presheaf.TotalCup.CechProduct.totalCup E L ν i j (AssemblyCoefficientCup.map F η E hE P i x) (AssemblyCoefficientCup.map F η E hE P j y) := by
  rw [map_eq, map_eq, map_eq]
  exact CechCoefficient.TotalCup.map_cup F η hη E hE K μ ν hprod i j x y

variable [F.PreservesHomology] [PreservesFiniteLimits F]

def homologyMap (n : ℕ) := CoefficientCochainCup.map F η (Presheaf.TotalCup.CechProduct.total E K) (Presheaf.TotalCup.CechProduct.total E L)
  (GeometricComparison.CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P).hom n

omit [PreservesFiniteLimits F] in
theorem homologyMap_eq (n : ℕ) :
    homologyMap F η E hE P n = CechCoefficient.CohomologyCup.Total.homologyMap F η E hE K n := by
  unfold homologyMap CechCoefficient.CohomologyCup.Total.homologyMap
  rw [GeometricComparison.CechAssembly.CoefficientCoordinates.CechAssemblyCoefficientCoordinates.hom]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.AssemblyCoefficientCup
