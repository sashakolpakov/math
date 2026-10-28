import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Equalizer

/-! # Coincidence Closed Point Test -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceClosedPointTest

noncomputable section

section

/-! Closing a coincidence locus from an open subscheme adds no
new points inside that open subscheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace OpenClosure

variable {X Y : Over (Spec (.of ℂ))} (U : X.left.Opens)
  (f g : Over.mk (U.ι ≫ X.hom) ⟶ Y) [IsSeparated Y.hom]

def openLocus : Closeds (U : Scheme) := Closed.Equalizer.locus f g

def locus : Closeds X.left :=
  ⟨closure (U.ι '' (openLocus U f g : Set (U : Scheme))), isClosed_closure⟩

theorem mem_on_open (x : U) :
    U.ι x ∈ locus U f g ↔ x ∈ Closed.Equalizer.locus f g := by
  have he := U.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
    (openLocus U f g : Set (U : Scheme))
  rw [(openLocus U f g).isClosed.closure_eq] at he
  exact (congrArg (fun S : Set (U : Scheme) => x ∈ S) he).to_iff.symm

theorem not_mem_of_ne (x : U) (hx : f.left x ≠ g.left x) : U.ι x ∉ locus U f g :=
  fun h => hx (Closed.Equalizer.eq_of_mem f g x ((mem_on_open U f g x).mp h))

theorem mem_iff_closed [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (x : U) (hx : IsClosed ({x} : Set (U : Scheme))) :
    U.ι x ∈ locus U f g ↔ f.left x = g.left x := by
  let : LocallyOfFiniteType (Over.mk (U.ι ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  exact (mem_on_open U f g x).trans (Closed.Equalizer.mem_iff_closed f g x hx)

end OpenClosure

end

/-! Inclusion of closed coincidence loci can be checked at closed
points on the open domain, using the Jacobson property over the complex field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem subset {X Y : Over (Spec (.of ℂ))} [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (f g : Over.mk (U.ι ≫ X.hom) ⟶ Y) [IsSeparated Y.hom]
    (S : Closeds X.left)
    (h : ∀ x : U, IsClosed ({x} : Set (U : Scheme)) →
      x ∈ OpenClosure.openLocus U f g → U.ι x ∈ S) :
    (OpenClosure.locus U f g : Set X.left) ⊆ S := by
  let : JacobsonSpace (U : Scheme) := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ X.hom)
  let A := OpenClosure.openLocus U f g
  have he : closure ((A : Set (U : Scheme)) ∩ closedPoints (U : Scheme)) = (A : Set (U : Scheme)) :=
    (JacobsonSpace.closure_inter_closedPoints_eq_closure A.isClosed.isLocallyClosed).trans A.isClosed.closure_eq
  have hs : (A : Set (U : Scheme)) ⊆ U.ι ⁻¹' (S : Set X.left) := by
    rw [← he]
    exact closure_minimal (fun x hx => h x hx.2 hx.1) (S.isClosed.preimage U.ι.continuous)
  change closure (U.ι '' (A : Set (U : Scheme))) ⊆ S
  apply closure_minimal _ S.isClosed
  rintro _ ⟨x, hx, rfl⟩
  exact hs hx

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceClosedPointTest
