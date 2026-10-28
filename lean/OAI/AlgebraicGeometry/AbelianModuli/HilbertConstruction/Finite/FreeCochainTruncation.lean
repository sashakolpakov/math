import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CochainTruncation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.CochainVanishing

/-! # Free Cochain Truncation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCochainTruncation

noncomputable section

/-! A residue cohomology bound gives a genuine finite free upper truncation of the local model. Its final term is the actual kernel of the next differential. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

def cochainCyclesKernelIso (C : CochainComplex (ModuleCat.{u} R) ℕ) (g : ℕ) :
    C.cycles g ≅ ModuleCat.of R (C.d g (g + 1)).hom.ker :=
  C.cyclesIsoSc' (g - 1) g (g + 1) (by cases g <;> simp) (CochainComplex.next ℕ g) ≪≫
    (C.sc' (g - 1) g (g + 1)).moduleCatCyclesIso

theorem finiteCochainTruncation_finite_free
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : IsZero ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex
      (.up ℕ)).obj C).homology (g + 1))) :
    ∀ q, Module.Finite R ((CochainTruncation.finiteCochainTruncation C g).X q) ∧
      Module.Free R ((CochainTruncation.finiteCochainTruncation C g).X q) := by
  obtain ⟨hfinK, hfreeK, _⟩ :=
    Residue.CochainVanishing.LocalSectionLifting.finiteFreeCochain_last_cycles_split_finite_free C hfin hfree g hres
  let : Module.Finite R (C.d g (g + 1)).hom.ker := hfinK
  let : Module.Free R (C.d g (g + 1)).hom.ker := hfreeK
  intro q
  rcases lt_trichotomy q g with hq | hq | hq
  · have : Module.Finite R (C.X q) := hfin q
    have : Module.Free R (C.X q) := hfree q
    let e := (CochainTruncation.finiteCochainTruncationXIso C g q hq).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · subst q
    let e := (CochainTruncation.finiteCochainTruncationLastIso C g ≪≫ cochainCyclesKernelIso C g).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have hz := CochainTruncation.finiteCochainTruncation_isZero_above C g q hq
    have : Subsingleton ((CochainTruncation.finiteCochainTruncation C g).X q) := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩

theorem finiteCochainTruncation_quasiIso_of_residue_bound
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : ∀ q, g < q → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex (.up ℕ)).obj C).homology q)) :
    QuasiIso (CochainTruncation.finiteCochainTruncationι C g) := by
  apply CochainTruncation.finiteCochainTruncation_quasiIso C g
  intro q hq
  have : Module.Finite R (C.sc q).X₁ := hfin ((ComplexShape.up ℕ).prev q)
  have : Module.Free R (C.sc q).X₁ := hfree ((ComplexShape.up ℕ).prev q)
  have : Module.Finite R (C.sc q).X₂ := hfin q
  have : Module.Free R (C.sc q).X₂ := hfree q
  have : Module.Finite R (C.sc q).X₃ := hfin ((ComplexShape.up ℕ).next q)
  have : Module.Free R (C.sc q).X₃ := hfree ((ComplexShape.up ℕ).next q)
  exact Local.ResidueExactness.LocalSectionLifting.finiteFreeShortComplex_exact_of_residue_exact (C.sc q)
    ((HomologicalComplex.exactAt_iff_isZero_homology _ q).mpr (hres q hq))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCochainTruncation
