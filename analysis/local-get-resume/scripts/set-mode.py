# Rewrite how a local-variable read resumes, in both DMCFA variants: lose | add | keep.
import sys, re
mode = sys.argv[1]
forms = {
 'lose': "          res <- apply kOp valAddr (dynamic retCtx)\n",
 'add':  "          d <- dLimit\n          m <- mLimit\n          res <- apply kOp valAddr (dynamic (newDelim d m (addCallRaw m retCtx bodId) bodId (getName varName)))\n",
 'keep': "          res <- apply kOp valAddr (localBodyDyn (getName varName) oCtx (dynamic retCtx))\n",
}
pat = re.compile(r"(?:          d <- dLimit\n          m <- mLimit\n)?          res <- apply kOp valAddr \([^\n]*\n(?=          returnV \$ handleLocal res venv bodId \(id, varName\) valAddr retCtx)")
for v in ['DMCFA', 'DMCFAR']:
    p = f'src/Core/FlowAnalysis/Full/{v}/DMCFA.hs'
    s = open(p).read()
    s, n = pat.subn(forms[mode], s)
    assert n == 1, (p, n)
    open(p, 'w').write(s)
print('mode', mode)
