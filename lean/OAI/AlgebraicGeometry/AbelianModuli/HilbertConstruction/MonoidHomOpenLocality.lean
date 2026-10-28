import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection

/-! # Monoid Hom Open Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality

noncomputable section

/-! The full group-homomorphism equations are local on an open cover of the base. Pointedness is preserved when transporting a map through group isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u v

theorem isMonHom_of_openCover
    {S : Scheme.{u}} {A B : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) (C : Scheme.OpenCover.{v} S)
    (h : ∀ i, IsMonHom ((Over.pullback (C.f i)).map f)) : IsMonHom f := by
  constructor
  · apply HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C
    intro i
    exact ((MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback (C.f i)) f).mp (h i)).1
  · apply HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C
    intro i
    exact ((MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback (C.f i)) f).mp (h i)).2

theorem pointedMap_comp {S : Scheme.{u}} {A B C : Over S} [MonObj A] [MonObj B] [MonObj C]
    (f : A ⟶ B) (g : B ⟶ C) (hf : η[A] ≫ f = η[B]) (hg : η[B] ≫ g = η[C]) :
    η[A] ≫ (f ≫ g) = η[C] :=
  (Category.assoc η[A] f g).symm.trans ((congrArg (fun z => z ≫ g) hf).trans hg)

theorem pointedMap_conjugate {S : Scheme.{u}} {A B A' B' : Over S}
    [MonObj A] [MonObj B] [MonObj A'] [MonObj B']
    (e : A ≅ A') (d : B ≅ B') [IsMonHom e.hom] [IsMonHom d.hom]
    (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) :
    η[A'] ≫ (e.inv ≫ f ≫ d.hom) = η[B'] :=
  pointedMap_comp e.inv (f ≫ d.hom) (IsMonHom.one_hom e.inv)
    (pointedMap_comp f d.hom hf (IsMonHom.one_hom d.hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
