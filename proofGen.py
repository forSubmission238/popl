import os
import argparse
from murphi2isabelle import translateFile
import json, csv
from generate import inv_2forall, trans_ref, json_str_gen

arg_parser = argparse.ArgumentParser(description='Generate Proof File')
arg_parser.add_argument('--task', default='mutualEx')
args = arg_parser.parse_args()

data_dir = '.'
protocol_name = args.task
#对协议文件格式上的修改以适应证明生成程序
inv_2forall(filename="{0}/{1}/ABS{1}.m".format(data_dir, protocol_name))
trans_ref(data_dir, args.task)

#获取抽象过程
csv_f = open('{}/{}/abs_process.csv'.format(data_dir, protocol_name), 'r')
reader = csv.reader(csv_f)
abs_result = dict()
for line in reader:
    abs_result[line[0]] = line[1:]

#生成json信息
filename = '{0}/{1}/ABS_ref_{1}.m'.format(data_dir, protocol_name)
assert os.path.exists(filename)
enum_type, rule_dict = json_str_gen(filename = filename)
os.remove(filename)

#加上加强的lemma
data = []
data.append(enum_type)
for k,v in rule_dict.items():
    data.append(v)
for d in data:
    if 'ruleset' in d:
        if d['ruleset'] in abs_result:
            d['strengthen'] = list(reversed(abs_result[d['ruleset']]))
        del d['limits']
        
with open('{0}/{1}/{1}_str.json'.format(data_dir, protocol_name), 'w') as f:
    json.dump(data, f, indent=4)

#生成证明文件
translateFile("{0}/{1}/ABS{1}.m".format(data_dir, protocol_name), "{0}/{1}/{1}_str.json".format(data_dir, protocol_name), "{}".format(protocol_name))

os.system('mv {0}/{1}.thy {0}/{1}/'.format(data_dir, protocol_name))