# Regenerates pure/qga_encode.thy from the locale interface of
# pure/QGA_on_GA.thy plus the three prose fragments in this directory.
# Run:  python pure/gen/gen_qga_encode.py
# The axiomatization block and the interpretation argument list are
# derived mechanically so that the two theories cannot drift apart.
import re, io, sys
import os
BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..') + '/'
GEN  = os.path.join(os.path.dirname(os.path.abspath(__file__)), '')
src = open(BASE + 'QGA_on_GA.thy', encoding='utf-8').read()
lines = src.split('\n')
CONC = ['qga_encoding','qga_subst','qga_dfns','qga_match','qga_struct_rule',
        'qga_prop_rule','qga_eq_rule','qga_nat_rule','qga_ind_rule','qga_quant_rule',
        'qga_cond_rule','qga_def_rule','qga_proof_check','qga_fuel_semantics',
        'qga_witnessed']
cur=None; fixes=[]; defs=[]
i=0
while i < len(lines):
    ln=lines[i]
    m=re.match(r'^locale (\w+)', ln)
    if m: cur=m.group(1)
    if cur in CONC:
        mf=re.match(r'^  fixes (\w+)\s*::\s*(".*")\s*$', ln)
        if mf: fixes.append((mf.group(1), mf.group(2)))
        md=re.match(r'^  assumes (\w+_def):\s*(.*)$', ln)
        if md:
            body=[md.group(2)]; q=md.group(2).count('"'); j=i
            while q%2==1 or q==0:
                j+=1; body.append(lines[j]); q+=lines[j].count('"')
            defs.append((md.group(1), '\n'.join(body))); i=j
    i+=1

ENC = {'tag_T','load_T','pack_T','tag_F','load_F','pack_F'}
SPECIAL = {'dfns','tBot'}
ax = [(n,t) for (n,t) in fixes if n not in ENC and n not in SPECIAL]
order = [n for (n,t) in fixes]

head = open(GEN + 'qga_encode_head.txt', encoding='utf-8').read()
tail = open(GEN + 'qga_encode_tail.txt', encoding='utf-8').read()

O = io.StringIO()
O.write(head)
O.write('\naxiomatization\n')
for idx,(n,t) in enumerate(ax):
    sep = ' and' if idx < len(ax)-1 else ''
    O.write('  %-20s :: %s%s\n' % (n, t, sep))
O.write('where\n')
for idx,(n,b) in enumerate(defs):
    sep = ' and' if idx < len(defs)-1 else ''
    O.write('  %s: %s%s\n\n' % (n, b, sep))
O.write(tail)
O.write('\ninterpretation qga: qga_full\n')
O.write('  ' + ' '.join(order) + '\n')
O.write('  apply unfold_locales\n')
O.write('  apply (fact pack_T_N tag_T_N load_T_N pack_F_N tag_F_N load_F_N\n')
O.write('              tag_pack_T load_pack_T pack_tag_T tag_pack_F load_pack_F pack_tag_F\n')
O.write('              decrease_T decrease_F tag_T_zero tag_F_zero mono_pack_T mono_pack_F\n')
O.write('              dfns_N tBot_N tBot_closed\n')
for k in range(0, len(defs), 4):
    O.write('              ' + ' '.join(n for n,_ in defs[k:k+4]) + '\n')
O.write('              )+\n  done\n')
O.write(open(GEN + 'qga_encode_end.txt', encoding='utf-8').read())
open(BASE + 'qga_encode.thy','w',encoding='utf-8').write(O.getvalue())
print('written', len(O.getvalue().split('\n')), 'lines;', len(order), 'params;', len(defs), 'defs')
