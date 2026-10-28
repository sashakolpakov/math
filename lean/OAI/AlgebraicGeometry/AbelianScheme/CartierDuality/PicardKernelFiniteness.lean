import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricKernel
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps

/-! # Picard Kernel Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness.Construction.KernelCharacters

noncomputable section

/-!
# CartierDuality: finiteness of geometric kernels of actual dual isogenies
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The kernel of pullback on actual line-bundle classes is invariant
under isomorphisms of the source and target schemes. -/
def pullbackKernelTransport
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : X' ≅ X) (b : Y' ≅ Y) (h : f' ≫ b.hom = a.hom ≫ f) :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y' // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f' q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X'} ↪
      {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X} where
  toFun q := ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass b.inv q.val, by
    have he : f ≫ b.inv = a.inv ≫ f' := by
      apply (cancel_epi a.hom).mp
      rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, q.property,
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]⟩
  inj' q r hqr := Subtype.ext ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso b.symm).injective (congrArg Subtype.val hqr))

/-- Removing the canonical product with the base identifies the geometric
Picard kernel with classes on the actual target abelian variety. -/
def geometricDualKernelNativeLineEmbedding
    {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme //
      x ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D E f = 1} ↪
      {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left //
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.scheme.left} :=
  (Picard.Homomorphisms.GeometricKernel.Construction.geometricDualKernelLineEmbedding D E f).trans
    (pullbackKernelTransport f.left ((𝟙_ (Over (Spec (.of k)))) ◁ f).left
      ((Over.forget _).mapIso (λ_ A.scheme)) ((Over.forget _).mapIso (λ_ B.scheme))
      (congrArg Over.Hom.left (leftUnitor_naturality f)))

/-- Finite faithfully flat group morphisms have finite actual line-class
pullback kernels over a field. -/
theorem finite_lineKernel_of_finite_flat
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsFinite f.left] [Flat f.left] [Surjective f.left] :
    Finite {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} := by
  have sq := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_isPullback f).map (Over.forget (Spec (.of k)))
  have hfin : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq (inferInstanceAs (IsFinite f.left))
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom
  let G : Grp (Over (Spec (.of k))) := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  have : IsFinite G.X.hom := hfin
  have : IsCommMonObj G.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f
  obtain ⟨R, hR, _, ⟨i⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  let e : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
    (Grp.forget (Over (Spec (.of k)))).mapIso i
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom i.hom.hom.hom)
  exact LineCharacterDetection.Construction.KernelCharacters.finite_pullbackKernel f R e

/-- The geometric kernel of the actual dual Picard pullback is finite
for every finite flat surjective homomorphism of abelian varieties. -/
theorem finite_geometric_dualKernel
    {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (E : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (f : A.scheme ⟶ B.scheme)
    [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left] :
    Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D E f)) := by
  have hfinite := finite_lineKernel_of_finite_flat f
  have : Finite {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme //
      x ≫ Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D E f = 1} :=
    Finite.of_injective _ (geometricDualKernelNativeLineEmbedding D E f).injective
  let q := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D E f
  let j : (Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme q) →
      {x : Over.mk (𝟙 (Spec (.of k))) ⟶ E.abelian.scheme // x ≫ q = 1} :=
    fun a => ⟨a ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion q, by rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]⟩
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q) := inferInstanceAs (Mono (equalizer.ι q 1))
  exact Finite.of_injective j (fun a b hab =>
    (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion q)).mp (congrArg Subtype.val hab))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardKernelFiniteness.Construction.KernelCharacters
