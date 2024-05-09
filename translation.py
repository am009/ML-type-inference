from wjkutil import *

# ==============翻译=================

from cachier import cachier
Eng2Chn2 = '''你是一个翻译助手。你将用户的英文输入直接翻译为中文。不要添加任何注解。
英文：{}
中文：'''

API_KEY = ""

@cachier()
def ask3(msg):
    from zhipuai import ZhipuAI
    client = ZhipuAI(api_key=API_KEY)
    response = client.chat.completions.create(
    model="glm-4",  # 填写需要调用的模型名称
    messages=[
            {"role": "user", "content": msg},
        ],
    )
    return response.choices[0].message.content

@cachier()
def ask3_stream_print(msg):
    from zhipuai import ZhipuAI
    client = ZhipuAI(api_key=API_KEY)
    response = client.chat.completions.create(
    model="glm-4",  # 填写需要调用的模型名称
    messages=[
            {"role": "user", "content": msg},
        ],
        stream=True,
    )
    result = ''
    for chunk in response:
        print(chunk.choices[0].delta.content, end='')
        result += chunk.choices[0].delta.content
    sys.stdout.flush()
    return result

def translate(text):
    return ask3_stream_print(Eng2Chn2.format(text))

content = read_file("mathpix/top-short-155.md")

content = content.split('\n\n')

translated_paras_pair = []

import time
for para in content:
    if (para.startswith('$$')): translated_paras_pair.append(para); continue
    if (para.startswith('|')): translated_paras_pair.append(para); continue
    if (para.startswith('![]')): translated_paras_pair.append(para); continue
    if (len(para) < 20): translated_paras_pair.append(para); continue
    print(f"======== 正在翻译：========\n{para}")
    print("============================")
    result = translate(para)
    translated_paras_pair.append((para, result))
    print("\n============================")

translated_eng = [i[1] if type(i) is tuple else i for i in translated_paras_pair ]
translated_mixed = [i[0] + '\n\n' + i[1] if type(i) is tuple else i for i in translated_paras_pair ]

write_file("translated.md", '\n\n'.join(translated_eng))
write_file("translated_mix.md", '\n\n'.join(translated_mixed))
