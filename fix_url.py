from wjkutil import *
import shutil, requests
md = read_file("translated_mix.md")

def download(url, save):
    r = requests.get(url, stream=True)
    if r.status_code == 200:
        with open(save, 'wb') as f:
            r.raw.decode_content = True
            shutil.copyfileobj(r.raw, f)

converted = []
for line in md.splitlines():
    if (line.startswith("![]")):
        url = line .removeprefix("![](")
        url = url.removesuffix(")")
        name = re.search(r'/([^/]+?\.jpg)', url).group(1)
        name = f'images/{name}'
        print(f"Download {url} to {name}")
        if not os.path.exists(name):
            download(url, name)
        line = f'![]({name})'
    converted.append(line)

write_file('translated_mix_fixurl.md', '\n'.join(converted))
