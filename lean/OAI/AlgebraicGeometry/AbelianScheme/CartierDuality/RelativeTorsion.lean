import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledGeometricKernel
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison

/-! # Relative Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsion

noncomputable section

/-!
# CartierDuality: torsion geometry without a fixed relative dimension

The hypotheses are the native smooth, proper, geometrically connected
commutative group scheme, its actual normalized Poincare representation,
and an actual finite isogeny to that dual.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.RelativeAbelian

/-- The actual geometric Picard kernel embeds into the actual pullback
kernel of line-bundle classes, without a dimension parameter. -/
def geometricDualKernelNativeLineEmbedding
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (f : A ⟶ B) [IsMonHom f] :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian //
      x ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f = 1} ↪
      {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} :=
  (Picard.Homomorphisms.UnbundledGeometricKernel.Construction.UnbundledPicard.geometricDualKernelLineEmbedding D E f).trans
    (PicardKernelFiniteness.Construction.KernelCharacters.pullbackKernelTransport f.left ((𝟙_ (Over (Spec (.of k)))) ◁ f).left
      ((Over.forget _).mapIso (λ_ A)) ((Over.forget _).mapIso (λ_ B))
      (congrArg Over.Hom.left (leftUnitor_naturality f)))

/-- Finite-flat descent detects the whole geometric dual kernel. -/
theorem finite_geometric_dualKernel
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (E : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (f : A ⟶ B)
    [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left] :
    Finite (Over.mk (𝟙 (Spec (.of k))) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f)) := by
  have := PicardKernelFiniteness.Construction.KernelCharacters.finite_lineKernel_of_finite_flat f
  have : Finite {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian //
      x ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f = 1} :=
    Finite.of_injective _ (geometricDualKernelNativeLineEmbedding D E f).injective
  let q := Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D E f
  let j : (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme q) →
      {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian // x ≫ q = 1} :=
    fun a => ⟨a ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion q, by rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]⟩
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q) := inferInstanceAs (Mono (equalizer.ι q 1))
  exact Finite.of_injective j (fun a b hab =>
    (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q)).mp (congrArg Subtype.val hab))

/-- The actual dual Frobenius has finite geometric kernel. -/
theorem finite_dualFrobenius_geometric_kernel
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    Finite (Over.mk (𝟙 (Spec (.of k))) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))) := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p Fact.out hS A
  let hF := Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p Fact.out hS A
  have : IsFinite F.left := hF.1.1
  have : Flat F.left := hF.1.2.1
  have : Surjective F.left := hF.2.1
  have hmon : IsMonHom F := Picard.Homomorphisms.Group.Construction.relativeFrobenius_isMonHom p Fact.out hS A
  exact @finite_geometric_dualKernel k inferInstance inferInstance A _
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    D (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out _ hS)) F hmon hF.1.1 hF.1.2.1 hF.2.1

/-- Characteristic-prime multiplication on the actual dual is finite. -/
theorem finite_dual_characteristic_power
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    IsFinite ((𝟙 D.abelian : D.abelian ⟶ D.abelian) ^ p).left := by
  have := finite_dualFrobenius_geometric_kernel p k A D
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let V := Picard.Homomorphisms.UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p Fact.out hS
  have hV : V = Picard.Homomorphisms.Verschiebung.Construction.verschiebung p k D.abelian :=
    Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualRelativeFrobenius_eq_verschiebung D p
  have : IsMonHom V := hV.symm ▸ inferInstanceAs (IsMonHom (Picard.Homomorphisms.Verschiebung.Construction.verschiebung p k D.abelian))
  have : IsProper (Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup D.abelian (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out _ hS)).hom :=
    inferInstanceAs (IsProper (pullback.snd D.abelian.hom (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p Fact.out _ hS)))
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme V).hom := Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Picard.Homomorphisms.Kernel.Construction.kernelScheme V)
  have hfinV : IsFinite V.left := Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel V
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p Fact.out hS D.abelian
  have hfinF : IsFinite F.left := Picard.Homomorphisms.Properties.Construction.relativeFrobenius_finite p Fact.out hS D.abelian
  have hFV : F.left ≫ V.left = ((𝟙 D.abelian) ^ p).left :=
    congrArg (fun a => a.left) (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.frobenius_dual_givenGroupPow D p Fact.out hS)
  exact hFV ▸ MorphismProperty.comp_mem (@IsFinite) F.left V.left hfinF hfinV

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A)

/-- All positive multiplication maps on the actual dual are finite over
any base, even when relative dimension varies between components. -/
theorem finite_positive_dual_power (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 D.abelian : D.abelian ⟶ D.abelian) ^ n).left := by
  apply GeometricFiniteness.Construction.Schemes.finite_positive_powers_of_geometric_characteristic_primes D.abelian _ n hn
  intro K _ _ a p hp hpK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpK
  have : Smooth ((Over.pullback a).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom a))
  have : IsProper ((Over.pullback a).obj A).hom := inferInstanceAs (IsProper (pullback.snd A.hom a))
  have : GeometricallyConnected ((Over.pullback a).obj A).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd A.hom a))
  exact finite_dual_characteristic_power p K ((Over.pullback a).obj A) (D.pullback a)

/-- A finite map to the actual dual transfers finiteness of multiplication. -/
theorem finite_positive_power (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left]
    (n : ℕ) (hn : 0 < n) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have := finite_positive_dual_power A D n hn
  exact MultiplicationReduction.Construction.Multiplication.finite_power_of_finite_hom ell n

/-- Every positive torsion sheaf of the actual dual is finite locally free. -/
theorem dual_torsionFppfAb_finiteLocallyFree (n : ℕ) (hn : 0 < n) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk D.abelian)) n) := by
  have := finite_positive_dual_power A D n hn
  exact TorsionGeometry.Construction.Schemes.torsionFppfAb_finiteLocallyFree_of_finite_power (Grp.mk D.abelian) n

/-- The actual torsion sheaf is finite locally free for all positive n. -/
theorem torsionFppfAb_finiteLocallyFree (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left]
    (n : ℕ) (hn : 0 < n) :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S
      (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk A)) n) := by
  have := finite_positive_power A D ell n hn
  exact TorsionGeometry.Construction.Schemes.torsionFppfAb_finiteLocallyFree_of_finite_power (Grp.mk A) n

/-- Coprimality of the actual fiber degree gives the canonical native
torsion isomorphism, with finite local freeness proved from geometry. -/
theorem torsionMap_isIso (ell : A ⟶ D.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n) (hdegree : ∀ s : S, n.Coprime (ell.left.finrank (η[D.abelian].left s))) :
    IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap ell n) := by
  have := finite_positive_power A D ell n hn
  have := finite_positive_dual_power A D n hn
  obtain ⟨hAf, hAflat, hAfp⟩ := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A) n
  obtain ⟨hBf, hBflat, hBfp⟩ := TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk D.abelian) n
  exact RelativeCoprimeTorsion.Construction.CoprimeTorsion.torsionMap_isIso_of_coprime_fiber_degree ell n hdegree

/-- The same isomorphism is the actual morphism of torsion fppf sheaves. -/
theorem torsionSheafMap_isIso (ell : A ⟶ D.abelian) [IsMonHom ell]
    [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
    (n : ℕ) (hn : 0 < n) (hdegree : ∀ s : S, n.Coprime (ell.left.finrank (η[D.abelian].left s))) :
    IsIso (SheafTorsionMaps.Construction.Schemes.torsionSheafMap (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
      (@Grp.homMk (Over S) _ _ (Grp.mk A) (Grp.mk D.abelian) ell inferInstance)) n) := by
  let f : Grp.mk A ⟶ Grp.mk D.abelian :=
    @Grp.homMk (Over S) _ _ (Grp.mk A) (Grp.mk D.abelian) ell inferInstance
  have : IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n) := torsionMap_isIso A D ell n hn hdegree
  exact SheafTorsionMaps.Construction.Schemes.torsionSheafMap_isIso_of_native f n

end Construction.RelativeAbelian

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeTorsion
