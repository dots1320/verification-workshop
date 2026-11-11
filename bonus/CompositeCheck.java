import org.cprover.CProver;

// 1. JBMC builds trees of NODES nodes by calling addChild on any pair of nodes
// allowed by its precondition, and checks the class invariant of every node after
// each call. --unwind K bounds the number of calls (and every other loop).
//   ./bmc CompositeCheck.addChildren --unwind 4 --no-unwinding-assertions
public class CompositeCheck {

    static final int NODES = 3;

    public static void addChildren() {
        Composite[] nodes = new Composite[NODES];
        for (int i = 0; i < NODES; i++) {
            nodes[i] = new Composite(CProver.nondetInt());
        }
        while (CProver.nondetBoolean()) {
            Composite p = nodes[anyIndex()];
            Composite c = nodes[anyIndex()];
            CProver.assume(c != p && c.parent == null);
            for (Composite ancestor = p; ancestor != null; ancestor = ancestor.parent) {
                CProver.assume(ancestor != c);       // addChild must not create a cycle
            }
            p.addChild(c);
            for (Composite n : nodes) {
                checkInvariant(n);
            }
        }
    }

    static int anyIndex() {
        int i = CProver.nondetInt();
        CProver.assume(0 <= i && i < NODES);
        return i;
    }

    // The class invariant of Composite, from the comments on its fields.
    static void checkInvariant(Composite n) {
        // A tree of NODES nodes must reach its root within NODES parent links.
        Composite ancestor = n;
        for (int depth = 0; depth < NODES && ancestor != null; depth++) {
            ancestor = ancestor.parent;
        }
        assert ancestor == null;                   // catches cycles explicitly

        int maximum = n.initValue;
        boolean hasMaxChild = false;
        for (Composite c = n.firstChild; c != null; c = c.nextSibling) {
            assert c.parent == n;                  // each child points back to its parent
            if (c.value > maximum) {
                maximum = c.value;
            }
            if (c == n.maxChild) {
                hasMaxChild = true;
            }
        }
        assert n.value == maximum;
        assert (n.maxChild == null) == (n.value == n.initValue);
        if (n.maxChild != null) {
            assert hasMaxChild;
            assert n.maxChild.value == n.value;
        }
    }
}
