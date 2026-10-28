import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantOpen
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenFrame
import Mathlib.Topology.Connected.Clopen

/-! # Product Constant Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantIs.Construction.ProductConstantTrivialityLocus

noncomputable section

/-! The trivial-fiber locus for a line bundle trivial on both constant
product axes is clopen. A single trivial fiber fills a connected base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] {A B X Y S : Scheme.{u}}
variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable [A.IsSeparated] [B.IsSeparated] [X.IsSeparated] [Y.IsSeparated]
variable (a : A ⟶ Spec (.of K)) (b : B ⟶ Spec (.of K))
variable (f : X ⟶ S) (g : Y ⟶ S) [(pullback f g).IsSeparated]
variable [IsProper f] [IsProper g] [Flat f] [Flat g]
variable [GeometricallyIntegral f] [GeometricallyIntegral g]
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ Spec (.of K))
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)
variable (PA : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk a))
variable (PB : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk b))
variable (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (pullback.fst f g ≫ f)))
variable {ι κ : Type u} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable (U : ι → A.Opens) (V : κ → B.Opens)
variable (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
variable (hcU : iSup U = ⊤) (hcV : iSup V = ⊤)
variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _) (sY : S ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
variable (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ (p ⁻¹ᵁ U i₀))
variable (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ (q ⁻¹ᵁ V j₀))
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (pullback f g))
variable (eX : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g sY hsY)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
variable (eY : (L.pullback (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g sX hsX)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

variable (hI : ∀ x : S, IsIntegral ((pullback.fst f g ≫ f).fiber x))

include hp hq PA PB P hU hV hcU hcV hi₀ hj₀ eX eY hI

theorem isOpen : IsOpen (ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.locus (pullback.fst f g ≫ f) L) := by
  apply OpenFrame.Construction.OpenFrameFibers.isOpen_of_neighborhoods
  intro x hx
  have := hI x
  exact ProductConstantOpen.Construction.ProductConstantFrameNeighborhood.exists_open a b f g p q t hp hq PA PB P
    U V hU hV hcU hcV sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY x hx

theorem isClopen : IsClopen (ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.locus (pullback.fst f g ≫ f) L) :=
  ⟨ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.isClosed (pullback.fst f g ≫ f) L P hI,
    isOpen a b f g p q t hp hq PA PB P U V hU hV hcU hcV
      sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY hI⟩

theorem all_fibers [ConnectedSpace S] (x₀ : S)
    (he : Nonempty ((L.pullback ((pullback.fst f g ≫ f).fiberι x₀)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f).fiber x₀))) :
    ∀ x : S, Nonempty ((L.pullback ((pullback.fst f g ≫ f).fiberι x)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((pullback.fst f g ≫ f).fiber x)) := by
  have hall := (isClopen a b f g p q t hp hq PA PB P U V hU hV hcU hcV
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ L eX eY hI).eq_univ ⟨x₀, he⟩
  intro x
  exact show x ∈ ProjectiveTriviality.Construction.ProjectiveTrivialityClosed.locus (pullback.fst f g ≫ f) L from
    hall.symm ▸ Set.mem_univ x

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductConstantIs.Construction.ProductConstantTrivialityLocus
