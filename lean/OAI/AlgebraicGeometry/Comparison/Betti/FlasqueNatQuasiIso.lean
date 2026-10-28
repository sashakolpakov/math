import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBoundedExactness
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct

/-! # Flasque Nat Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso

noncomputable section

section

/-!
# Open sections preserve quasi-isomorphisms of bounded-below flasque complexes

The cone has flasque degree objects and is acyclic. The proved section
exactness theorem and the canonical cone comparison then give the result.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem cone_acyclic_iff {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (CochainComplex.mappingCone f).Acyclic ↔ QuasiIso f := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).symm.trans
    ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)).symm

variable {X : TopCat.{0}} {K L : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℤ} (f : K ⟶ L)

theorem cone_flasque (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((CochainComplex.mappingCone f).X n) := by
  have := hK (n + 1)
  have := hL n
  have := FlasqueBiproduct.biprod_flasque (K.X (n + 1)) (L.X n)
  exact FlasqueBiproduct.flasque_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm

/-- The section functor preserves the actual comparison under the stated geometric sheaf properties. -/
theorem sections_quasiIso (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n))
    (k l : ℤ) (hKbound : ∀ n, n < k → IsZero (K.X n))
    (hLbound : ∀ n, n < l → IsZero (L.X n)) (hf : QuasiIso f) (U : Opens X) :
    QuasiIso (((FlasqueBiproduct.sections U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hcone := (cone_acyclic_iff f).mpr hf
  have hbound : ∀ n, n < min (k - 1) l → IsZero ((CochainComplex.mappingCone f).X n) := by
    intro n hn
    exact (CochainComplex.mappingCone.isZero_X_iff f n).mpr
      ⟨hKbound (n + 1) (by omega), hLbound n (by omega)⟩
  have hs := FlasqueBoundedExactness.bounded_sections_acyclic (CochainComplex.mappingCone f)
    (cone_flasque f hK hL) hcone (min (k - 1) l) hbound U
  apply (cone_acyclic_iff _).mp
  intro n
  exact (hs n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f (FlasqueBiproduct.sections U))

end

/-! The nonnegative-complex form of the proved flasque section comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}}

theorem flasque_of_isZero (F : FlasqueBiproduct.ComplexSheaves X) (hF : IsZero F) : TopCat.Sheaf.IsFlasque F := by
  constructor
  intro U V i
  have hzero := ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj V).map_isZero
    ((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).map_isZero hF)
  exact hzero.epi (F.obj.map i)

theorem extend_flasque (K : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (i : ℤ) :
    TopCat.Sheaf.IsFlasque ((K.extend (ComplexShape.embeddingUpIntGE 0)).X i) := by
  classical
  let e := ComplexShape.embeddingUpIntGE 0
  change TopCat.Sheaf.IsFlasque (HomologicalComplex.extend.X K (e.r i))
  cases h : e.r i with
  | none => exact flasque_of_isZero _ (isZero_zero _)
  | some n => exact hK n

theorem extend_zero_below (K : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((K.extend (ComplexShape.embeddingUpIntGE 0)).X i) :=
  K.isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i
    ((ComplexShape.notMem_range_embeddingUpIntGE_iff 0 i).mpr hi)

/-- Actual open sections preserve a quasi-isomorphism between nonnegative flasque complexes. -/
theorem nat_sections_quasiIso {K L : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℕ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (hf : QuasiIso f) (U : Opens X) :
    QuasiIso (((FlasqueBiproduct.sections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  let e := ComplexShape.embeddingUpIntGE 0
  have hfe : QuasiIso (HomologicalComplex.extendMap f e) :=
    (HomologicalComplex.quasiIso_extendMap_iff f e).mpr hf
  have he := sections_quasiIso (HomologicalComplex.extendMap f e)
    (extend_flasque K hK) (extend_flasque L hL) 0 0 (extend_zero_below K) (extend_zero_below L) hfe U
  let a := Complex.Extension.mapExtendIso (FlasqueBiproduct.sections U) e K
  let b := Complex.Extension.mapExtendIso (FlasqueBiproduct.sections U) e L
  let ei : Arrow.mk (((FlasqueBiproduct.sections U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap f e)) ≅
      Arrow.mk (HomologicalComplex.extendMap
        (((FlasqueBiproduct.sections U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) e) :=
    Arrow.isoMk a b (Complex.Extension.mapExtendIso_naturality (FlasqueBiproduct.sections U) e f).symm
  apply (HomologicalComplex.quasiIso_extendMap_iff _ e).mp
  exact (quasiIso_iff_of_arrow_mk_iso _ _ ei).mp he

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso
