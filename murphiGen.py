import os
import argparse
from abstract import initAbs, doMurphiCheck, test_abs_str


arg_parser = argparse.ArgumentParser(description='Learning based CMP')
arg_parser.add_argument('--task', default='mutualEx')
args = arg_parser.parse_args()

data_dir = '.'
protocol_name = args.task
#删除旧有的抽象协议
if os.path.exists('./{0}/ABS{0}.m'.format(protocol_name)):
    os.remove('./{0}/ABS{0}.m'.format(protocol_name))
#删除旧有的加强记录
if os.path.exists("{}/{}/abs_process.csv".format(data_dir, protocol_name)):
    os.remove("{}/{}/abs_process.csv".format(data_dir, protocol_name))

#生成新的抽象协议
initAbs("./{0}/{0}.m".format(protocol_name), "./ABS{0}.m".format(protocol_name))

#自动加强
checked = []
flag , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)

inv_num = 1
while flag != None:
    inv_num = test_abs_str(flag = flag, name = protocol_name,inv_num= inv_num)
    flag  , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)
print("success!")

os.system('mv ./ABS{0}.m ./{0}/'.format(protocol_name))