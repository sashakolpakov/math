import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.SheafOpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso

/-! # Frobenius Charts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCharts

noncomputable section

/-!
# IntegralComparison: the original global Frobenius terms have coherent restrictions on the actual finite cover
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

def opens (i : EtaleCover.Index k X) : X.left.Opens :=
  CechIntersections.opens k X 0 (fun _ => i)

omit [Fintype k] in
theorem opens_eq (i : EtaleCover.Index k X) :
    opens k X i = DeRhamZariski.opens k X i := by
  rw [opens, CechIntersections.eq_iInf]
  exact iInf_const

omit [Fintype k] in
theorem cover : ⨆ i, opens k X i = ⊤ := by
  simp only [opens_eq]
  exact DeRhamZariski.cover k X

omit [Fintype k] in
theorem affine (i : EtaleCover.Index k X) : IsAffineOpen (opens k X i) :=
  CechIntersections.affine k X 0 (fun _ => i)

def ring (i : EtaleCover.Index k X) : CommAlgCat.{u} k :=
  CechIntersections.coordinateRing k X 0 (fun _ => i)

def chart (i : EtaleCover.Index k X) : Spec (CommRingCat.of (ring k X i)) ⟶ X.left :=
  CechIntersections.chartMap k X 0 (fun _ => i)

instance chart_open (i : EtaleCover.Index k X) : IsOpenImmersion (chart k X i) :=
  CechIntersections.chartMap_open k X 0 (fun _ => i)

def restricted (i : EtaleCover.Index k X) (n : ℕ) : (Spec (CommRingCat.of (ring k X i))).Modules :=
  @Scheme.Modules.restrict (Spec (CommRingCat.of (ring k X i))) X.left
    ((Frobenius.DeRhamGlobal.complex k X).X n) (chart k X i) (chart_open k X i)

def iso (i : EtaleCover.Index k X) (n : ℕ) :
    (Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k (ring k X i))).X n ≅
      restricted k X i n :=
  @Frobenius.SheafOpenRestriction.iso k inferInstance inferInstance
    (Crystalline.Presentation.affineScheme k (ring k X i)) X
    (chart k X i) (chart_open k X i) (CechIntersections.chartMap_over k X 0 (fun _ => i)) n

theorem affine_quasicoherent (i : EtaleCover.Index k X) (n : ℕ) :
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k (ring k X i))).X n).IsQuasicoherent := by
  let σ := EtaleCover.coordinateIndex k X i
  let : LinearOrder σ := ChartSections.coordinateOrder k X i
  let : Algebra (MvPolynomial σ k) (ring k X i) := CechIntersections.polynomialAlgebra k X 0 (fun _ => i)
  let : IsScalarTower k (MvPolynomial σ k) (ring k X i) := CechIntersections.tower k X 0 (fun _ => i)
  let : Algebra.Etale (MvPolynomial σ k) (ring k X i) := CechIntersections.etale k X 0 (fun _ => i)
  exact Affine.FrobeniusCoherence.quasicoherent k (ring k X i) σ n

theorem affine_finiteType (i : EtaleCover.Index k X) (n : ℕ) :
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k (ring k X i))).X n).IsFiniteType := by
  let σ := EtaleCover.coordinateIndex k X i
  let : LinearOrder σ := ChartSections.coordinateOrder k X i
  let : Fintype σ := EtaleCover.coordinateIndex_fintype k X i
  let : Algebra (MvPolynomial σ k) (ring k X i) := CechIntersections.polynomialAlgebra k X 0 (fun _ => i)
  let : IsScalarTower k (MvPolynomial σ k) (ring k X i) := CechIntersections.tower k X 0 (fun _ => i)
  let : Algebra.Etale (MvPolynomial σ k) (ring k X i) := CechIntersections.etale k X 0 (fun _ => i)
  exact Affine.FrobeniusCoherence.finiteType_etale k (ring k X i) σ n

theorem quasicoherent (i : EtaleCover.Index k X) (n : ℕ) :
    (restricted k X i n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (ring k X i))).ringCatSheaf).prop_of_iso (iso k X i n)
    (affine_quasicoherent k X i n)

theorem finiteType (i : EtaleCover.Index k X) (n : ℕ) :
    (restricted k X i n).IsFiniteType :=
  @Module.FiniteTypeIso.finiteType (Spec (CommRingCat.of (ring k X i)))
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k (ring k X i))).X n)
    (restricted k X i n) (iso k X i n) (affine_finiteType k X i n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCharts
