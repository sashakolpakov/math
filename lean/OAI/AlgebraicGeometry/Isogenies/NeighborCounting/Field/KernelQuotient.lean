import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotientSheafCokernel

/-! # Kernel Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.KernelQuotient

noncomputable section

/-! Construct the actual finite-flat subgroup quotient over a field,
retaining its dimension, projection, and complete scheme-theoretic kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (H : Grp (Over (Spec (.of k)))) (i : H.X ⟶ A.scheme) [IsMonHom i]

def fieldKernelQuotient (hi : IsClosedImmersion i.left)
    (hH : IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom) :
    AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction.GeometricKernelQuotient A H i := Classical.choice (by
  let A' : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of k)) := {
    toOver := A.scheme
    group := A.group
    commutative := A.commutative
    proper := A.proper
    smooth := inferInstance
    connected := A.connected }
  obtain ⟨B, f, hf, hfinite, hsurj, hkernel, _⟩ :=
    Quotients.FiniteDescent.Scheme.Construction.exists_abelian_scheme_quotient (Spec (.of k)) A' H.X i hi hH
  exact ⟨⟨B, f, hf, hfinite.1, hfinite.2.1, hfinite.2.2, hsurj, hkernel⟩⟩)

variable {A H i}

def fieldAbelian (Q : AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction.GeometricKernelQuotient A H i) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)) := by
  let B : Picard.PoincareBundle.Epi.Construction.AbelianScheme (Spec (.of k)) := {
    toOver := Q.target.toOver
    group := Q.target.group
    commutative := Q.target.commutative
    proper := Q.target.proper
    smooth := Q.target.smooth
    geometricallyConnected := Q.target.connected }
  exact AbelianScheme.IsogenyQuotient.Dimension.Construction.abelianQuotientWithDimension A B Q.projection

def fieldIsogeny (Q : AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction.GeometricKernelQuotient A H i) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A (fieldAbelian Q) where
  hom := Q.projection
  preservesGroup := Q.groupHom
  finite := Q.finite
  flat := Q.flat
  surjective := Q.surjective

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.KernelQuotient
