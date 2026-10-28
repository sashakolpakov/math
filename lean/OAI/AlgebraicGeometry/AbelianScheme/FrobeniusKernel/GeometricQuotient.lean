import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupAffine
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Quotient

/-! # Geometric Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction

noncomputable section

/-!
Construct geometric quotients by finite flat subgroup schemes. Finite
translation orbits have affine neighborhoods because the smooth connected
proper group is integral and translations move finitely many points into
one affine open. Thus the remaining orbit hypothesis of FiniteDescent is proved.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
variable (H : Grp (Over (Spec (.of K)))) (i : H.X ⟶ A.scheme) [IsMonHom i]

omit [IsMonHom i] in
/-- The affine-orbit hypothesis is a theorem on the geometric abelian
fiber, including for nonreduced subgroup schemes. -/
theorem geometricKernel_affine_orbits [IsFinite H.X.hom] :
    ∀ x : A.scheme.left, ∃ U : A.scheme.left.Opens, IsAffineOpen U ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (snd H.X A.scheme).left
        (Quotients.FiniteDescent.Epi.Construction.translation i).left x y → y ∈ U := by
  have : IsFinite (snd H.X A.scheme).left :=
    inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd H.X.hom A.scheme.hom))
  intro x
  obtain ⟨U, hU, hsub⟩ := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.exists_affineOpen_of_finite A.scheme
    {y | Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related (snd H.X A.scheme).left (Quotients.FiniteDescent.Epi.Construction.translation i).left x y}
    (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.finite_orbit _ _ x)
  exact ⟨U, hU, fun y hy => hsub hy⟩

/-- The native scheme quotient, its group structure, and its exact kernel
are constructed from the specified embedded finite locally free subgroup. -/
theorem exists_geometricKernelQuotient
    (hi : IsClosedImmersion i.left)
    (hH : IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom) :
    ∃ (B : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of K))) (f : A.scheme ⟶ B.toOver),
      IsMonHom f ∧ Quotients.FiniteDescent.AbelianQuotient.Construction.FiniteLocallyFree f.left ∧ Surjective f.left ∧
      (∀ (T : Over (Spec (.of K))) (a : T ⟶ A.scheme),
        a ≫ f = 1 ↔ ∃! h : T ⟶ H.X, h ≫ i = a) ∧
      (∀ (T : Over (Spec (.of K))) (f' : A.scheme ⟶ T),
        (∀ (U : Over (Spec (.of K))) (a : U ⟶ A.scheme) (h : U ⟶ H.X),
          ((h ≫ i) * a) ≫ f' = a ≫ f') →
        ∃! b : B.toOver ⟶ T, f ≫ b = f') := by
  let A' : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of K)) :=
    { toOver := A.scheme, group := A.group, commutative := A.commutative,
      proper := A.proper, smooth := inferInstance, connected := A.connected }
  have : IsFinite H.X.hom := hH.1
  exact Quotients.FiniteDescent.AbelianQuotient.Construction.exists_abelian_scheme_quotient_of_affine_orbits (Spec (.of K)) A' H.X i hi hH
    (geometricKernel_affine_orbits A H i)

/-- A constructed geometric quotient, retaining its actual projection
and scheme-theoretic kernel rather than only its isomorphism class. -/
structure GeometricKernelQuotient where
  target : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of K))
  projection : A.scheme ⟶ target.toOver
  groupHom : IsMonHom projection
  finite : IsFinite projection.left
  flat : Flat projection.left
  finitelyPresented : LocallyOfFinitePresentation projection.left
  surjective : Surjective projection.left
  kernel : Prescribed.Construction.PrescribedKernel projection i

attribute [instance] GeometricKernelQuotient.groupHom GeometricKernelQuotient.finite
  GeometricKernelQuotient.flat GeometricKernelQuotient.finitelyPresented
  GeometricKernelQuotient.surjective

def geometricKernelQuotient
    (hi : IsClosedImmersion i.left)
    (hH : IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom) :
    GeometricKernelQuotient A H i :=
  Classical.choice (by
    obtain ⟨B, f, hf, hfinite, hsurj, hker, _⟩ := exists_geometricKernelQuotient A H i hi hH
    exact ⟨⟨B, f, hf, hfinite.1, hfinite.2.1, hfinite.2.2, hsurj, hker⟩⟩)

namespace GeometricKernelQuotient

variable {A H i} (Q : GeometricKernelQuotient A H i) [Mono i]

/-- The quotient scheme represents the independently constructed fppf
subgroup quotient, with its full infinitesimal test-scheme behavior. -/
def sheafIso : BaseChange.Construction.subgroupQuotient i ≅ (BaseChange.Construction.fppfPoints (Spec (.of K))).obj Q.target.toOver :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms Q.projection i Q.kernel
    (Picard.Homomorphisms.Quotient.Construction.isFppfQuotientByKernel_of_fppf Q.projection)

omit [IsAlgClosed K] [IsMonHom i] in
theorem sheafIso_projection :
    Prescribed.Construction.subgroupQuotientProjection i ≫ Q.sheafIso.hom =
      (BaseChange.Construction.fppfPoints (Spec (.of K))).map Q.projection :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms_projection Q.projection i Q.kernel
    (Picard.Homomorphisms.Quotient.Construction.isFppfQuotientByKernel_of_fppf Q.projection)

end GeometricKernelQuotient

/-- Apply the quotient construction to the assembled chosen/opposite
kernel. Both finite flatness and closedness are supplied by proved kernel
assembly theorems, including the actual opposite-annihilator factors. -/
def fullPairedGeometricQuotient (n k : ℕ)
    (G H B : Fin k → Grp (Over (Spec (.of K))))
    (P : ∀ v, CartierModel.Construction.CartierCoordinates (.of K) (G v))
    (Q : ∀ v, CartierModel.Construction.CartierCoordinates (.of K) (H v))
    (i : ∀ v, H v ⟶ G v) (pairing : ∀ v, B v ≅ (P v).dualGroup)
    (split : Assembly.Construction.torsionGroup A n ≅ BlockProducts.Construction.groupBlockProduct k (fun v => G v ⊗ B v))
    (hi : ∀ v, IsClosedImmersion (i v).hom.hom.left)
    (hH : ∀ v, IsFinite (H v).X.hom ∧ Flat (H v).X.hom ∧
      LocallyOfFinitePresentation (H v).X.hom) :
    GeometricKernelQuotient A (BlockProducts.Construction.groupBlockProduct k (fun v => (P v).pairedKernel (Q v) (i v)))
      (PairedKernels.Construction.fullPairedKernelToAbelian A n k G H B P Q i pairing split) :=
  geometricKernelQuotient A _ _
    (PairedKernels.Construction.fullPairedKernelToAbelian_closed A n k G H B P Q i pairing split hi)
    (PairedKernels.Construction.fullPairedKernel_finiteLocallyFree k G H P Q i hH)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotient.Construction
