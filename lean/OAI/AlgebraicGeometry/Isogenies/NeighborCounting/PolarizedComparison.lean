import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Polarization
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced

/-! # Polarized Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison

noncomputable section

/-!
The canonical same-kernel comparison preserves the actual polarization,
integral action and ordered marking. Polarization compatibility is derived
from the Poincare-defined dual maps and the two multiplier identities.
The complementary dual map is constructed by fpqc descent.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Dual
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction

variable {K R : Type u} [Field K] [IsAlgClosed K] [CommRing R] {d N n : ℕ}
variable {A B C : AbelianScheme.TateComparison.PEL.PELFamilyData R d N (Spec (.of K))}

local instance epi_isogeny {X Y : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of K))}
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny X Y) : Epi f.hom := by
  have : EffectiveEpi f.hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc f.hom
  infer_instance

omit [IsAlgClosed K] in
theorem pel_dualMap (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) :
    f.dualHom = DualComparison.dualMap A.dual B.dual f.isogeny.hom := by
  apply DualComparison.dualMap_eq_of_poincare
  simpa only [id_tensorHom, tensorHom_id] using f.poincare

omit [IsAlgClosed K] in
/-- Comparing the same full kernel constructs a group-scheme isomorphism.
Its compatibility with both actual dual maps follows from Picard functoriality. -/
theorem quotientIso_dual_intertwines (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny) :
    DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom ≫ f.dualHom =
      g.dualHom := by
  simp only [pel_dualMap f, pel_dualMap g, ← DualComparison.dualMap_comp, QuotientComparison.quotientIso_projection]

/-- Equality of the source multiplier identities forces equality of the
target polarization morphisms under the constructed quotient isomorphism. -/
theorem quotientIso_preserves_polarization
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny)
    [IsFinite f.dualHom.left] [Flat f.dualHom.left] [Surjective f.dualHom.left]
    (hdualKernel : ∀ (T : Over (Spec (.of K))) (x : T ⟶ B.dual.abelian.scheme),
      x ≫ f.dualHom = 1 → x ^ n = 1)
    [Epi ((𝟙 B.abelian.scheme) ^ n)] :
    B.polarizationMap.hom =
      (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom ≫ C.polarizationMap.hom ≫
        DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom := by
  let fd : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B.dual.abelian A.dual.abelian := {
    hom := f.dualHom
    preservesGroup := inferInstance
    finite := inferInstance
    flat := inferInstance
    surjective := inferInstance }
  obtain ⟨gd, _, hfdgd, _⟩ := AbelianScheme.FrobeniusKernel.Power.Construction.exists_complementary_isogeny_map fd n hdualKernel
  have : IsMonHom (DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom) :=
    Dual.dualMap_isMonHom _ _ _
  apply AbelianScheme.IsogenyQuotient.Polarization.Construction.polarization_pullback_injective n f.isogeny.hom f.dualHom gd hfdgd
  rw [f.polarization]
  simpa only [Category.assoc, quotientIso_dual_intertwines,
    ← Category.assoc f.isogeny.hom, QuotientComparison.quotientIso_projection] using g.polarization.symm

/-- Finiteness of the native dual map suffices for polarization comparison:
finite-kernel rigidity on the connected reduced abelian target removes
the need to assume a complementary dual map or its torsion bound. -/
theorem quotientIso_preserves_polarization_of_finite_dual
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny) [IsFinite f.dualHom.left] :
    B.polarizationMap.hom =
      (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom ≫ C.polarizationMap.hom ≫
        DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom := by
  have : IsReduced B.abelian.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field B.abelian.scheme.hom
  have : ConnectedSpace B.abelian.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.abelian.scheme.hom
  have : IsMonHom (DualComparison.dualMap B.dual C.dual (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom) :=
    Dual.dualMap_isMonHom _ _ _
  apply AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction.polarizationPullback_injective f.isogeny.hom f.dualHom
  rw [f.polarization]
  simpa only [Category.assoc, quotientIso_dual_intertwines,
    ← Category.assoc f.isogeny.hom, QuotientComparison.quotientIso_projection] using g.polarization.symm

omit [IsAlgClosed K] in
theorem quotientIso_preserves_pelMarking
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny)
    (T : Over (Spec (.of K)))
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * d) → ZMod N))) :
    (B.marking.hom.app (.op T) c).val ≫ (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom =
      (C.marking.hom.app (.op T) c).val := by
  rw [← f.marking, Category.assoc, QuotientComparison.quotientIso_projection, g.marking]

omit [IsAlgClosed K] in
theorem quotientIso_preserves_pelAction
    (f : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A B n) (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny A C n)
    (hk : QuotientComparison.SameKernel f.isogeny g.isogeny) (r : R) :
    AbelianScheme.TateComparison.End.endSchemeMap B.abelian.scheme (B.action r) ≫ (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom =
      (QuotientComparison.quotientIso f.isogeny g.isogeny hk).hom ≫ AbelianScheme.TateComparison.End.endSchemeMap C.abelian.scheme (C.action r) := by
  apply (cancel_epi f.isogeny.hom).mp
  rw [← Category.assoc, ← f.equivariant, Category.assoc, QuotientComparison.quotientIso_projection,
    ← Category.assoc, QuotientComparison.quotientIso_projection, g.equivariant]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedComparison
